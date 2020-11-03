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
  stdOptions,
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
import qualified Data.Text.IO as TIO (hGetContents, putStrLn)
import Data.TPTP (TPTP)
import Data.TPTP.Parse.Text (parseTSTPOnly)
import Data.TPTP.Pretty (pretty)
import System.IO (Handle, hPutStr, hFlush, hClose)
import System.Process (ProcessHandle, runInteractiveProcess)

import ATP.Error
import ATP.FOL (ClauseSet, Theorem)
import ATP.Codec.TPTP (encodeClauseSet, encodeTheorem, decodeSolution)
import ATP.Prover (Prover(..), proverCmd, eprover)
import ATP.Proof


data ProvingOptions = ProvingOptions {
  prover :: Prover,
  displayTPTP :: Bool,
  displayCmd  :: Bool,
  displayTSTP :: Bool
} deriving (Eq, Show, Ord)

stdOptions :: ProvingOptions
stdOptions = ProvingOptions {
  prover = defaultProver,
  displayTPTP = False,
  displayCmd  = False,
  displayTSTP = False
}

-- | The default prover used by 'prove'.
defaultProver :: Prover
defaultProver = eprover

-- | Attempt to refute a set of clauses using 'defaultProver'.
refute :: ClauseSet -> IO Answer
refute = refuteWith stdOptions

-- | Attempt to refute a set of clauses using a given prover.
refuteUsing :: Prover -> ClauseSet -> IO Answer
refuteUsing p = refuteWith stdOptions{prover = p}

-- | Attempt to refute a set of clauses with a given set of options.
refuteWith :: ProvingOptions -> ClauseSet -> IO Answer
refuteWith po = runWith po . encodeClauseSet

-- | Attempt to prove a theorem using 'defaultProver'.
prove :: Theorem -> IO Answer
prove = proveWith stdOptions

-- | Attempt to prove a theorem using a given prover.
proveUsing :: Prover -> Theorem -> IO Answer
proveUsing p = proveWith stdOptions{prover = p}

-- | Attempt to prove a theorem with a given set of options.
proveWith :: ProvingOptions -> Theorem -> IO Answer
proveWith po = runWith po . encodeTheorem

runWith :: ProvingOptions -> TPTP -> IO Answer
runWith ProvingOptions{prover, displayTPTP, displayCmd, displayTSTP} problem = do
  -- Execute the theorem prover and open handlers to its stdin and stdout
  (hStdIn, hStdOut, _, _) <- startProverProcess prover

  -- Encode the given theorem in TPTP and write it to the prover's stdin
  let tptp = pretty problem
  when displayTPTP (print tptp)
  when displayCmd (putStrLn $ proverCmd prover)
  hPutStr hStdIn (show tptp) >> hFlush hStdIn >> hClose hStdIn

  -- Read the response of the theorem prover
  output <- TIO.hGetContents hStdOut
  when displayTSTP (TIO.putStrLn output)

  -- Parse the response of the theorem prover
  let solution = parseProverOutput output
  return $ Answer prover solution

parseProverOutput :: Text -> Partial Solution
parseProverOutput output = case parseTSTPOnly output of
  Left e  -> parsingError e
  Right s -> decodeSolution s

startProverProcess :: Prover -> IO (Handle, Handle, Handle, ProcessHandle)
startProverProcess Prover{cmdPath, cmdArgs} =
  runInteractiveProcess cmdPath cmdArgs Nothing Nothing
