{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleInstances #-}

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

instance {-# OVERLAPPABLE #-} (Simplify e, Arbitrary e) => Arbitrary (Simplified e) where
  arbitrary = Simplified . simplify <$> arbitrary
  shrink = traverse (fmap simplify . shrink)

instance Arbitrary f => Arbitrary (Simplified (Inference f)) where
  arbitrary = do
    i <- Inference <$> arbitrary <*> fmap getSimplified arbitrary
    return (Simplified i)

instance Arbitrary f => Arbitrary (Simplified (Sequent f)) where
  arbitrary = do
    s <- Sequent <$> arbitrary <*> fmap getSimplified arbitrary
    return (Simplified s)

instance (Ord f, Arbitrary f) => Arbitrary (Simplified (Derivation f)) where
  arbitrary = do
    d <- Derivation . fmap getSimplified <$> arbitrary
    return (Simplified d)

instance (Ord f, Arbitrary f) => Arbitrary (Simplified (Refutation f)) where
  arbitrary = do
    r <- Refutation <$> fmap getSimplified arbitrary <*> arbitrary
    return (Simplified r)
