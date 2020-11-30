{-# LANGUAGE CPP #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

{-|
Module       : ATP.FirstOrder.Problem
Description  : Problems in unsorted first-order logic.
Copyright    : (c) Evgenii Kotelnikov, 2019-2020
License      : GPL-3
Maintainer   : evgeny.kotelnikov@gmail.com
Stability    : experimental
-}

module ATP.FirstOrder.Problem (
  -- * Clause sets
  ClauseSet(..),

  -- * Theorems
  Theorem(..),
  (|-),
  pattern Claim,

  -- * Solutions
  Solution(..)
) where

import qualified Data.Foldable as Foldable (toList)
#if !MIN_VERSION_base(4, 11, 0)
import Data.Semigroup (Semigroup(..))
#endif

import ATP.FirstOrder.Core
import ATP.FirstOrder.Derivation


-- * Clause sets

-- | A clause set is zero or more first-order clauses.
-- The empty clause set is logically equivalent to falsum.
newtype ClauseSet = ClauseSet [Clause]
  deriving (Show, Eq, Ord, Semigroup, Monoid)


-- * Theorems

-- | A theorem is zero or more axioms and a conjecture.
data Theorem = Theorem {
  axioms :: [Formula],
  conjecture :: Formula
} deriving (Show, Eq, Ord)

infix 2 |-

-- | Syntactic sugar, a synonym for 'Theorem'.
(|-) :: Foldable f => f Formula -> Formula -> Theorem
as |- c = Theorem (Foldable.toList as) c

-- | A logical claim is a conjecture entailed by the empty set of axioms.
pattern Claim :: Formula -> Theorem
pattern Claim f = Theorem [] f

-- * Solution

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
