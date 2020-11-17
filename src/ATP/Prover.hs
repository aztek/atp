{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE LambdaCase #-}

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
  vendorName,
  Prover(..),
  proverCommand,
  proverArguments,
  vampire,
  eprover
) where

import Data.Text (Text)


-- | The automated theorem prover.
data Prover = Prover {
  vendor :: Vendor,
  executable :: FilePath
} deriving (Eq, Show, Ord)

data Vendor
  = E
  | Vampire
  deriving (Eq, Show, Ord, Enum, Bounded)

vendorName :: Vendor -> Text
vendorName = \case
  E -> "E"
  Vampire -> "Vampire"

proverCommand :: Prover -> Int -> String
proverCommand Prover{vendor, executable} timeLimit =
  unwords (executable:proverArguments vendor timeLimit)

-- | Build a command that executes the given prover.
proverArguments :: Vendor -> Int -> [String]
proverArguments vendor timeLimit = case vendor of
  E       -> ["--proof-object", "--silent", "--soft-cpu-limit=" ++ show timeLimit]
  Vampire -> ["--proof", "tptp", "--statistics", "none", "--time_limit", show timeLimit]

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
