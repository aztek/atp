{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}

{-|
Module       : ATP.Prove
Description  : Interface to automated theorem provers.
Copyright    : (c) Evgenii Kotelnikov, 2019-2021
License      : GPL-3
Maintainer   : evgeny.kotelnikov@gmail.com
Stability    : experimental

Interface to automated theorem provers.
-}

module ATP.Prove (
  ProvingOptions(..),
  defaultOptions,
  refute,
  refuteUsing,
  refuteWith,
  prove,
  proveUsing,
  proveWith
) where

import Control.Monad (when)
import Data.Text (Text)
import qualified Data.Text as T (pack)
import Data.TPTP (TPTP)
import Data.TPTP.Parse.Text (parseTSTPOnly)
import Data.TPTP.Pretty (pretty)
import System.Exit (ExitCode(..))
import System.Process (readProcessWithExitCode)
import Text.PrettyPrint.ANSI.Leijen (bold, text)

import ATP.Error
import ATP.FOL (Clauses, Theorem, Solution)
import ATP.Codec.TPTP (encodeClauses, encodeTheorem, decodeSolution)
import ATP.Prover


-- | The options that describe what theorem prover to use for a problem and
-- how to run it.
data ProvingOptions = ProvingOptions {
  prover      :: Prover,
  timeLimit   :: TimeLimit,
  memoryLimit :: MemoryLimit,
  debug       :: Bool -- ^ If @True@, print the input, the cli command,
                      --   the exit code and the output of the prover
} deriving (Eq, Show, Ord)

-- | The default options used by 'refute' and 'prove'.
--
-- >>> defaultOptions
-- ProvingOptions {prover = Prover {vendor = E, executable = "eprover"}, timeLimit = 300, memoryLimit = 2000, debug = False}
defaultOptions :: ProvingOptions
defaultOptions = ProvingOptions {
  prover = defaultProver,
  timeLimit = 300,
  memoryLimit = 2000,
  debug = False
}

-- | Attempt to refute a set of clauses using 'defaultProver'.
--
-- > refute = refuteWith defaultOptions
refute :: Clauses -> IO (Partial Solution)
refute = refuteWith defaultOptions

-- | Attempt to refute a set of clauses using a given prover.
refuteUsing :: Prover -> Clauses -> IO (Partial Solution)
refuteUsing p = refuteWith defaultOptions{prover = p}

-- | Attempt to refute a set of clauses with a given set of options.
refuteWith :: ProvingOptions -> Clauses -> IO (Partial Solution)
refuteWith opts = runWith opts . encodeClauses

-- | Attempt to prove a theorem using 'defaultProver'.
--
-- > prove = proveWith defaultOptions
prove :: Theorem -> IO (Partial Solution)
prove = proveWith defaultOptions

-- | Attempt to prove a theorem using a given prover.
proveUsing :: Prover -> Theorem -> IO (Partial Solution)
proveUsing p = proveWith defaultOptions{prover = p}

-- | Attempt to prove a theorem with a given set of options.
proveWith :: ProvingOptions -> Theorem -> IO (Partial Solution)
proveWith opts = runWith opts . encodeTheorem

runWith :: ProvingOptions -> TPTP -> IO (Partial Solution)
runWith opts tptp = do
  let ProvingOptions{prover} = opts
  let Prover{vendor} = prover
  let input = show (pretty tptp)
  (exitCode, stdout, stderr) <- runProver opts input
  let output = proverOutput vendor exitCode stdout stderr
  let solution = output >>= parseSolution
  return solution

runProver :: ProvingOptions -> String -> IO (ExitCode, Text, Text)
runProver opts input = do
  let ProvingOptions{prover, timeLimit, memoryLimit, debug} = opts
  let Prover{vendor, executable} = prover
  let arguments = proverArguments vendor timeLimit memoryLimit
  let debugPrint header str = when debug $
                              print (bold (text header)) >>
                              putStrLn str >> putStr "\n"
  debugPrint "Input" input
  debugPrint "Command" $ unwords (executable:arguments)
  (exitCode, stdout, stderr) <- readProcessWithExitCode executable arguments input
  debugPrint "Exit code" (show exitCode)
  debugPrint "Standard output" stdout
  debugPrint "Standard error"  stderr
  return (exitCode, T.pack stdout, T.pack stderr)

parseSolution :: Text -> Partial Solution
parseSolution = either parsingError decodeSolution . parseTSTPOnly
