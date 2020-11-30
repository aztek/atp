{-|
Module       : ATP.FirstOrder.Solution
Description  : Solutions to first-order problems.
Copyright    : (c) Evgenii Kotelnikov, 2019-2020
License      : GPL-3
Maintainer   : evgeny.kotelnikov@gmail.com
Stability    : experimental
-}

module ATP.FirstOrder.Solution (
  Solution(..)
) where

import ATP.FirstOrder.Derivation


-- | The solution produced by an automated first-order theorem prover.
data Solution
  = Saturation (Derivation Integer)
  -- ^ A theorem can be disproven if the prover constructs a saturated set of
  -- firt-order clauses.
  | Proof (Refutation Integer)
  -- ^ A theorem can be proven if the prover derives contradiction (the empty
  -- clause) from the set of axioms and the negated conjecture.
  deriving (Show, Eq, Ord)
