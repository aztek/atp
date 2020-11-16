{-# LANGUAGE NamedFieldPuns #-}

{-|
Module       : ATP.Prove
Description  : Interface for calling an automated theorem prover.
Copyright    : (c) Evgenii Kotelnikov, 2019
License      : GPL-3
Maintainer   : evgeny.kotelnikov@gmail.com
Stability    : experimental
-}

module ATP.Prove (
  ProvingOptions(..),
  defaultOptions,
  defaultProver,
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
import ATP.Error
import ATP.FOL (ClauseSet, Theorem)
import ATP.Codec.TPTP (encodeClauseSet, encodeTheorem, decodeSolution)
import ATP.Prover (Prover(..), proverCmd, eprover)
import ATP.Proof


data ProvingOptions = ProvingOptions {
  prover :: Prover,
  debug :: Bool
} deriving (Eq, Show, Ord)

-- | The default options used by 'refute' and 'prove'.
defaultOptions :: ProvingOptions
defaultOptions = ProvingOptions {
  prover = defaultProver,
  debug = False
}

-- | The default prover used by 'refute' and 'prove'.
defaultProver :: Prover
defaultProver = eprover

-- | Attempt to refute a set of clauses using 'defaultProver'.
refute :: ClauseSet -> IO Answer
refute = refuteWith defaultOptions

-- | Attempt to refute a set of clauses using a given prover.
refuteUsing :: Prover -> ClauseSet -> IO Answer
refuteUsing p = refuteWith defaultOptions{prover = p}

-- | Attempt to refute a set of clauses with a given set of options.
refuteWith :: ProvingOptions -> ClauseSet -> IO Answer
refuteWith opts = runWith opts . encodeClauseSet

-- | Attempt to prove a theorem using 'defaultProver'.
prove :: Theorem -> IO Answer
prove = proveWith defaultOptions

-- | Attempt to prove a theorem using a given prover.
proveUsing :: Prover -> Theorem -> IO Answer
proveUsing p = proveWith defaultOptions{prover = p}

-- | Attempt to prove a theorem with a given set of options.
proveWith :: ProvingOptions -> Theorem -> IO Answer
proveWith opts = runWith opts . encodeTheorem

runWith :: ProvingOptions -> TPTP -> IO Answer
runWith opts tptp = do
  let input = show (pretty tptp)
  (exitCode, output, err) <- runProver opts input

  let solution = case exitCode of
                   ExitSuccess -> parseOutput output
                   ExitFailure code -> exitCodeError code err

  return (Answer (prover opts) solution)

runProver :: ProvingOptions -> String -> IO (ExitCode, Text, Text)
runProver opts input = do
  let ProvingOptions{prover, debug} = opts
  let Prover{cmdPath, cmdArgs} = prover
  let printDebug str = when debug (putStrLn str >> putStrLn (replicate 80 '-'))

  printDebug input
  printDebug (proverCmd prover)
  (exitCode, output, err) <- readProcessWithExitCode cmdPath cmdArgs input
  printDebug output

  return (exitCode, T.pack output, T.pack err)

parseOutput :: Text -> Partial Solution
parseOutput = either parsingError decodeSolution . parseTSTPOnly
