{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE CPP #-}

{-|
Module       : ATP.FirstOrder.Derivation
Description  : Derivations in first-order logic.
Copyright    : (c) Evgenii Kotelnikov, 2019-2020
License      : GPL-3
Maintainer   : evgeny.kotelnikov@gmail.com
Stability    : experimental
-}

module ATP.FirstOrder.Derivation (
  -- * Proofs
  Rule(..),
  Inference(..),
  antecedents,
  consequent,
  Contradiction(..),
  Sequent(..),
  Derivation(..),
  addSequent,
  breadthFirst,
  labeling,
  Refutation(..)
) where

import Data.Foldable (toList)
import Data.Function (on)
import Data.List (sortBy)
import qualified Data.Map as M (fromList, insert, toList)
import Data.Map (Map, (!))
#if !MIN_VERSION_base(4, 11, 0)
import Data.Semigroup (Semigroup)
#endif
import Data.Text (Text)

import ATP.FirstOrder.Core


-- * Proofs

-- | The inference rule.
data Rule f
  = Axiom
  | Conjecture
  | NegatedConjecture  f
  | Flattening         f
  | Skolemisation      f
  | EnnfTransformation f
  | NnfTransformation  f
  | Clausification     f
  | TrivialInequality  f
  | Superposition         f f
  | Resolution            f f
  | Paramodulation        f f
  | SubsumptionResolution f f
  | ForwardDemodulation   f f
  | BackwardDemodulation  f f
  | AxiomOfChoice
  | Unknown    [f]
  | Other Text [f]
  deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

-- | A logical inference is an expression of the form
--
-- > A_1 ... A_n
-- > ----------- R,
-- >     C
--
-- where each of @A_1@, ... @A_n@ (called 'antecedents'), and @C@
-- (called 'consequent') are formulas and @R@ is an inference 'Rule'.
data Inference f = Inference (Rule f) LogicalExpression
  deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

-- | The antecedents of an inference.
antecedents :: Inference f -> [f]
antecedents (Inference rule _) = toList rule

-- | The consequent of an inference.
consequent :: Inference f -> LogicalExpression
consequent (Inference _ e) = e

-- | Contradiction is a special case of an inference whos consequent is
-- a logical falsum.
newtype Contradiction f = Contradiction (Rule f)
  deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

data Sequent f = Sequent f (Inference f)
  deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

sequentMap :: Ord f => [Sequent f] -> Map f (Inference f)
sequentMap ss = M.fromList [(f, e) | Sequent f e <- ss]

-- | Construct a mapping between inference labels and their correspondent
-- formulas.
labeling :: Ord f => [Sequent f] -> Map f LogicalExpression
labeling = fmap consequent . sequentMap

newtype Derivation f = Derivation (Map f (Inference f))
  deriving (Show, Eq, Ord, Semigroup, Monoid)

addSequent :: Ord f => Derivation f -> Sequent f -> Derivation f
addSequent (Derivation m) (Sequent f i) = Derivation (M.insert f i m)

fromDerivation :: Derivation f -> [Sequent f]
fromDerivation (Derivation m) = fmap (uncurry Sequent) (M.toList m)

breadthFirst :: Ord f => Derivation f -> [Sequent f]
breadthFirst d = sortBy (compare `on` criteria) (fromDerivation d)
  where criteria (Sequent l (Inference r f)) = (distances d ! l, r, f)

distances :: Ord f => Derivation f -> Map f Integer
distances (Derivation m) = fmap distance m
  where
    distance i
      | null (antecedents i) = 0
      | otherwise = 1 + maximum (fmap (\a -> distance (m ! a)) (antecedents i))

data Refutation f = Refutation (Derivation f) (Contradiction f)
  deriving (Show, Eq, Ord)
