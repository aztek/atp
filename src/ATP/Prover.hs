{-# LANGUAGE OverloadedStrings #-}

{-|
Module       : ATP.Prover
Description  : Models of automated theorem provers.
Copyright    : (c) Evgenii Kotelnikov, 2019
License      : GPL-3
Maintainer   : evgeny.kotelnikov@gmail.com
Stability    : experimental
-}

module ATP.Prover (
  Prover(..),
  vampire,
  eprover
) where

import Data.Text (Text)


-- | The automated theorem prover.
data Prover = Prover {
  proverName :: Text,
  cmdPath :: String,
  cmdArgs :: [String]
} deriving (Show, Eq, Ord)

-- | The <http://www.eprover.org/ E> theorem prover.
eprover :: Prover
eprover = Prover "E" "eprover" ["-p", "-s"]

-- | The <https://vprover.github.io/ Vampire> theorem prover.
vampire :: Prover
vampire = Prover "Vampire" "vampire" ["-p", "tptp"]