{-|
Module       : ATP.Proof
Description  : Solutions to first-order problems.
Copyright    : (c) Evgenii Kotelnikov, 2019
License      : GPL-3
Maintainer   : evgeny.kotelnikov@gmail.com
Stability    : experimental
-}

module ATP.Proof (
  Answer(..),
  Solution(..)
) where

import ATP.FOL
import ATP.Prover


-- | The proof by refutation with additional meta information such as which
-- prover found it.
data Answer = Answer {
  proofMeta :: Prover,
  solution :: Solution
} deriving (Show, Eq, Ord)

-- | The successful solution produced by an automated theorem prover for
-- first-order logic.
data Solution
  = Saturation (Derivation Integer)
  -- ^ A theorem can be disproven if the prover constructs a saturated set of
  -- firt-order clauses.
  | Proof (Refutation Integer)
  -- ^ A theorem can be proven if the prover derives contradiction (the empty
  -- clause) from the set of axioms and the negated conjecture.
  deriving (Show, Eq, Ord)
