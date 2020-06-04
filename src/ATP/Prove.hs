{-# LANGUAGE OverloadedStrings #-}
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
  prove,
  proveUsing,
  proveWith
) where

import Control.Monad (when)
import qualified Data.Text.IO as TIO (hGetContents, putStrLn)
import Data.TPTP.Parse.Text (parseTSTPOnly)
import Data.TPTP.Pretty (pretty)
import System.IO (Handle, hPutStr, hFlush, hClose)
import System.Process (ProcessHandle, runInteractiveProcess)

import ATP.FOL (Theorem)
import ATP.Codec.TPTP (encodeTheorem, decodeSolution)
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

-- | Attempt to prove a theorem using 'defaultProver'.
prove :: Theorem -> IO Answer
prove = proveWith stdOptions

-- | Attempt to prove a theorem using a given prover.
proveUsing :: Prover -> Theorem -> IO Answer
proveUsing p = proveWith stdOptions{prover = p}

proveWith :: ProvingOptions -> Theorem -> IO Answer
proveWith ProvingOptions{prover, displayTPTP, displayCmd, displayTSTP} theorem = do
  -- Execute the theorem prover and open handlers to its stdin and stdout
  (hStdIn, hStdOut, _, _) <- startProverProcess prover

  -- Encode the given theorem in TPTP and write it to the prover's stdin
  let tptp = pretty (encodeTheorem theorem)

  when displayTPTP (print tptp)

  when displayCmd (putStrLn $ proverCmd prover)

  hPutStr hStdIn (show tptp) >> hFlush hStdIn >> hClose hStdIn

  -- Read the response of the theorem prover
  output <- TIO.hGetContents hStdOut

  when displayTSTP (TIO.putStrLn output)

  case parseTSTPOnly output of
    Left err   -> error $ "proveWith: malformed proof: " ++ err
    Right tstp -> return $ Answer prover (decodeSolution tstp)

startProverProcess :: Prover -> IO (Handle, Handle, Handle, ProcessHandle)
startProverProcess Prover{cmdPath, cmdArgs} =
  runInteractiveProcess cmdPath cmdArgs Nothing Nothing
