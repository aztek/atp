{-# LANGUAGE LambdaCase #-}

{-|
Module       : ATP.FirstOrder.Conversion
Description  : Conversions between first-order expressions.
Copyright    : (c) Evgenii Kotelnikov, 2019-2021
License      : GPL-3
Maintainer   : evgeny.kotelnikov@gmail.com
Stability    : experimental
-}

module ATP.FirstOrder.Conversion (
  -- * Conversions
  -- ** Formulas
  liftSignedLiteral,
  unliftSignedLiteral,
  liftClause,
  unliftClause,

  -- ** Proofs
  liftContradiction,
  unliftContradiction,
  liftRefutation,
  unliftRefutation
) where

import qualified Data.Map as M (partition, toList)

import ATP.FirstOrder.Core
import ATP.FirstOrder.Derivation
import ATP.FirstOrder.Occurrence


-- * Conversions

-- ** Formulas

-- | Convert a clause to a full first-order formula.
liftClause :: Clause -> Formula
liftClause = \case
  EmptyClause -> Falsum
  Literals ls -> close . foldl1 (Connected Or) . fmap liftSignedLiteral $ ls

-- | Try to convert a first-order formula /f/ to a clause.
-- This function succeeds if /f/ is a tree of disjunctions of
-- (negated) atomic formula.
unliftClause :: Formula -> Maybe Clause
unliftClause = unlift . unprefix
  where
    unlift = \case
      Connected Or f g -> mappend <$> unlift f <*> unlift g
      f -> UnitClause <$> unliftSignedLiteral f

-- | Convert a signed literal to a (negated) atomic formula.
liftSignedLiteral :: Signed Literal -> Formula
liftSignedLiteral (Signed s l) = case s of
  Positive -> Atomic l
  Negative -> Negate (Atomic l)

-- | Try to convert a first-order formula /f/ to a signed literal.
-- This function succeeds if /f/ is a (negated) atomic formula.
unliftSignedLiteral :: Formula -> Maybe (Signed Literal)
unliftSignedLiteral = \case
  Atomic l -> Just (Signed Positive l)
  Negate f -> sign Negative <$> unliftSignedLiteral f
  _ -> Nothing


-- ** Proofs

-- | Convert a contradiction to an inference.
liftContradiction :: Contradiction f -> Inference f
liftContradiction (Contradiction r) = Inference r (Formula Falsum)

-- | Try to convert an inference to a contradiction.
unliftContradiction :: Inference f -> Maybe (Contradiction f)
unliftContradiction (Inference r e)
  | isContradiction e = Just (Contradiction r)
  | otherwise = Nothing

-- | Check whether a given expression is either a falsum or an empty clause.
isContradiction :: LogicalExpression -> Bool
isContradiction = \case
  Clause c | Falsum <- liftClause c -> True
  Formula Falsum -> True
  _ -> False

-- | Convert a refutation to a derivation.
liftRefutation :: Ord f => f -> Refutation f -> Derivation f
liftRefutation f (Refutation d c) = addSequent d (Sequent f (liftContradiction c))

-- | Try to convert a derivation to a refutation.
-- This function succeds if the derivation has exactly one inference
-- resulting in contradiction.
unliftRefutation :: Derivation f -> Maybe (Refutation f)
unliftRefutation (Derivation is) = Refutation (Derivation is') <$> c
  where
    (cs, is') = M.partition (isContradiction . consequent) is
    c | [(_, Inference r _)] <- M.toList cs = Just (Contradiction r)
      | otherwise = Nothing
