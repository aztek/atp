{-# LANGUAGE DeriveTraversable #-}

{-|
Module       : QuickCheckSpec.Generators
Description  : QuickCheck generators of simplified first-order expressions.
Copyright    : (c) Evgenii Kotelnikov, 2020
License      : GPL-3
Maintainer   : evgeny.kotelnikov@gmail.com
Stability    : experimental
-}

module QuickCheckSpec.Generators.Simplified (
  Simplified(..)
) where

import Test.QuickCheck (Arbitrary(..))

import QuickCheckSpec.Generators.FOL ()

import ATP.FOL


newtype Simplified a = Simplified { getSimplified :: a }
  deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

instance (Simplify e, Arbitrary e) => Arbitrary (Simplified e) where
  arbitrary = Simplified . simplify <$> arbitrary
  shrink = traverse (fmap simplify . shrink)
