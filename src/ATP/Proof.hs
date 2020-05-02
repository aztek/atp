{-|
Module       : ATP.Proof
Description  : Proofs of theorems.
Copyright    : (c) Evgenii Kotelnikov, 2019
License      : GPL-3
Maintainer   : evgeny.kotelnikov@gmail.com
Stability    : experimental
-}

module ATP.Proof (
  Proof(..),
) where

import ATP.FOL
import ATP.Prover


-- | The proof by refutation with additional meta information such as which
-- prover found it.
data Proof = Proof {
  proofMeta :: Prover,
  refutation :: Refutation Integer
} deriving (Show, Eq, Ord)
