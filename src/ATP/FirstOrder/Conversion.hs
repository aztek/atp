{-# LANGUAGE LambdaCase #-}

{-|
Module       : ATP.FirstOrder.Conversion
Description  : Conversions between first-order expressions.
Copyright    : (c) Evgenii Kotelnikov, 2019-2020
License      : GPL-3
Maintainer   : evgeny.kotelnikov@gmail.com
Stability    : experimental
-}

module ATP.FirstOrder.Conversion (
  -- * Conversions
  liftSignedLiteral,
  unliftSignedLiteral,
  liftClause,
  unliftClause
) where

import ATP.FirstOrder.Formula
import ATP.FirstOrder.Occurrence


-- * Conversions

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
      f -> fmap (\l -> Literals [l]) (unliftSignedLiteral f)

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
