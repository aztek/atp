{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE NamedFieldPuns #-}

{-|
Module       : ATP.Prover
Description  : Models of automated theorem provers.
Copyright    : (c) Evgenii Kotelnikov, 2019
License      : GPL-3
Maintainer   : evgeny.kotelnikov@gmail.com
Stability    : experimental
-}

module ATP.Prover (
  Vendor(..),
  Prover(..),
  proverCommand,
  proverArguments,
  vampire,
  eprover
) where


-- | The automated theorem prover.
data Prover = Prover {
  vendor :: Vendor,
  executable :: FilePath
} deriving (Eq, Show, Ord)

-- | The implementation of a theorem prover, supported by @atp@.
data Vendor
  = E
  | Vampire
  deriving (Eq, Show, Ord, Enum, Bounded)

-- | Build the command that executes the given prover.
proverCommand :: Prover -> Int -> Int -> String
proverCommand Prover{vendor, executable} timeLimit memoryLimit =
  unwords (executable:proverArguments vendor timeLimit memoryLimit)

-- | Build the list of command line arguments for the given prover.
proverArguments :: Vendor -> Int -> Int -> [String]
proverArguments vendor timeLimit memoryLimit = case vendor of
  E       -> ["--proof-object",
              "--silent",
              "--soft-cpu-limit=" ++ show timeLimit,
              "--memory-limit=" ++ show memoryLimit]

  Vampire -> ["--proof", "tptp",
              "--statistics", "none",
              "--time_limit", show timeLimit,
              "--memory_limit", show memoryLimit]

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
