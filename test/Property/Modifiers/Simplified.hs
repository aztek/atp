{-# LANGUAGE DeriveTraversable #-}

{-|
Module       : Property.Modifiers.Simplified
Description  : QuickCheck generators of simplified first-order expressions.
Copyright    : (c) Evgenii Kotelnikov, 2019-2021
License      : GPL-3
Maintainer   : evgeny.kotelnikov@gmail.com
Stability    : experimental
-}

module Property.Modifiers.Simplified (
  Simplified(..)
) where

import Test.QuickCheck (Arbitrary(..))

import Property.Generators ()

import ATP.FOL


newtype Simplified a = Simplified { getSimplified :: a }
  deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

instance (Simplify e, Arbitrary e) => Arbitrary (Simplified e) where
  arbitrary = Simplified . simplify <$> arbitrary
  shrink = traverse (fmap simplify . shrink)
