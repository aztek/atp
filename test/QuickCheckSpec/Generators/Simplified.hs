{-# LANGUAGE DeriveFunctor #-}
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

import Test.QuickCheck (Arbitrary(..), oneof)

import QuickCheckSpec.Generators.FOL ()

import ATP.FOL
import ATP.Proof


newtype Simplified a = Simplified { getSimplified :: a }
  deriving (Show, Eq, Ord, Functor)


-- * Formulas

instance Arbitrary (Simplified Formula) where
  arbitrary = Simplified . simplify <$> arbitrary

instance Arbitrary (Simplified LogicalExpression) where
  arbitrary = oneof [
      Simplified . Clause <$> arbitrary,
      fmap Formula <$> arbitrary
    ]


-- * Theorems

instance Arbitrary (Simplified Theorem) where
  arbitrary = do
    as <- fmap getSimplified <$> arbitrary
    c <- getSimplified <$> arbitrary
    return $ Simplified (Theorem as c)


-- * Proofs

instance Arbitrary l => Arbitrary (Simplified (Derivation l)) where
  arbitrary = do
    d <- Derivation <$> arbitrary <*> fmap getSimplified arbitrary
    return (Simplified d)

instance Arbitrary l => Arbitrary (Simplified (Refutation l)) where
  arbitrary = do
    r <- Refutation <$> arbitrary <*> fmap (fmap getSimplified) arbitrary
    return (Simplified r)
