{-|
Module       : ATP.FirstOrder.Theorem
Description  : Theorems in unsorted first-order logic.
Copyright    : (c) Evgenii Kotelnikov, 2019-2020
License      : GPL-3
Maintainer   : evgeny.kotelnikov@gmail.com
Stability    : experimental
-}

module ATP.FirstOrder.Theorem (
  -- * Theorems
  Theorem(..),
  (|-),
  claim
) where

import qualified Data.Foldable as Foldable (toList)

import ATP.FirstOrder.Formula


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

-- | Build a logical claim - a conjecture entailed by the empty set of premises.
claim :: Formula -> Theorem
claim f = [] |- f
