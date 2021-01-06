{-# LANGUAGE OverloadedStrings #-}

{-|
Module       : ATP.Prover
Description  : Models of automated theorem provers.
Copyright    : (c) Evgenii Kotelnikov, 2019-2021
License      : GPL-3
Maintainer   : evgeny.kotelnikov@gmail.com
Stability    : experimental

Models of automated theorem provers.
-}

module ATP.Prover (
  Vendor(..),
  Prover(..),
  TimeLimit,
  MemoryLimit,
  proverArguments,
  proverOutput,
  vampire,
  eprover,
  cvc4,
  defaultProver
) where

import Data.Text (Text)
import qualified Data.Text as T (isInfixOf)
import System.Exit (ExitCode(..))

import ATP.Error


-- | The automated theorem prover.
data Prover = Prover {
  vendor :: Vendor,
  executable :: FilePath
} deriving (Eq, Show, Ord)

-- | The implementation of a theorem prover, supported by @atp@.
data Vendor
  = E
  | Vampire
  | CVC4
  deriving (Eq, Show, Ord, Enum, Bounded)

-- | The time limit allocated to the prover, in seconds.
type TimeLimit = Int

-- | The memory limit allocated to the prover, in Mb.
type MemoryLimit = Int

-- | Build the list of command line arguments for the given prover.
proverArguments :: Vendor -> TimeLimit -> MemoryLimit -> [String]
proverArguments E timeLimit memoryLimit =
  ["--proof-object",
   "--silent",
   "--soft-cpu-limit=" ++ show timeLimit,
   "--memory-limit=" ++ show memoryLimit]
proverArguments Vampire timeLimit memoryLimit =
  ["--proof", "tptp",
   "--statistics", "none",
   "--time_limit", show timeLimit,
   "--memory_limit", show memoryLimit]
proverArguments CVC4 timeLimit _memoryLimit =
  ["-L", "tptp",
   "--proof", "--dump-proof", "--output-lang=tptp",
   "--tlimit=" ++ show (timeLimit * 1000)]

-- | Interpret the output of the theorem prover from its exit code and
-- the contents of the returned stdout and stderr.
proverOutput :: Vendor
             -> ExitCode
             -> Text -- ^ Standard out
             -> Text -- ^ Standard error
             -> Partial Text
proverOutput E exitCode stdout stderr = case exitCode of
  ExitSuccess   -> return stdout
  ExitFailure 1 -> return stdout
  ExitFailure 8 -> timeLimitError
  ExitFailure c -> exitCodeError c stderr
proverOutput Vampire exitCode stdout stderr = case exitCode of
  ExitSuccess   -> return stdout
  ExitFailure 1
    | "Time limit reached"    `T.isInfixOf` stdout -> timeLimitError
    | "Memory limit exceeded" `T.isInfixOf` stdout -> memoryLimitError
  ExitFailure c -> exitCodeError c stderr
proverOutput CVC4 exitCode stdout stderr = case exitCode of
  ExitSuccess   -> return stdout
  ExitFailure c -> exitCodeError c stderr

-- | The <http://www.eprover.org/ E> theorem prover.
eprover :: Prover
eprover = Prover {
  vendor = E,
  executable = "eprover"
}

-- | The <https://vprover.github.io/ Vampire> theorem prover.
vampire :: Prover
vampire = Prover {
  vendor = Vampire,
  executable = "vampire"
}

cvc4 :: Prover
cvc4 = Prover {
  vendor = CVC4,
  executable = "cvc4"
}

-- | The default prover used by @refute@ and @prove@.
--
-- >>> defaultProver
-- Prover {vendor = E, executable = "eprover"}
defaultProver :: Prover
defaultProver = eprover
