{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE CPP #-}

{-|
Module       : QuickCheckSpec.Generators
Description  : QuickCheck generators of first-order formulas.
Copyright    : (c) Evgenii Kotelnikov, 2019
License      : GPL-3
Maintainer   : evgeny.kotelnikov@gmail.com
Stability    : experimental
-}

module QuickCheckSpec.Generators (
  Simplified(..)
) where

#if !MIN_VERSION_base(4, 8, 0)
import Control.Applicative (pure, (<$>), (<*>))
#endif

import GHC.Generics (Generic)
import Generic.Random (genericArbitraryU, genericArbitraryRec, (%))

import Data.Text (Text, pack)
import Test.QuickCheck (Arbitrary(..), shrinkList, listOf1, choose)

import ATP.FOL
import ATP.Proof


-- * Helper type wrappers

newtype Simplified a = Simplified { getSimplified :: a }
  deriving (Show, Eq, Ord)

instance Arbitrary (Simplified Formula) where
  arbitrary = Simplified . simplify <$> arbitrary

instance Arbitrary (Simplified Theorem) where
  arbitrary = do
    as <- fmap getSimplified <$> arbitrary
    c <- getSimplified <$> arbitrary
    return $ Simplified (Theorem as c)

instance Arbitrary l => Arbitrary (Simplified (Derivation l)) where
  arbitrary = do
    d <- Derivation <$> arbitrary <*> fmap getSimplified arbitrary
    return (Simplified d)

instance Arbitrary l => Arbitrary (Simplified (Refutation l)) where
  arbitrary = do
    r <- Refutation <$> arbitrary <*> fmap (fmap getSimplified) arbitrary
    return (Simplified r)


-- * Formulas

instance Arbitrary Text where
  arbitrary = pack <$> listOf1 (choose ('a', 'z'))

deriving instance Generic Term
instance Arbitrary Term where
  arbitrary = genericArbitraryRec (1 % 1 % ())
  shrink = \case
    Variable _    -> []
    Function f ts -> ts ++ (Function f <$> shrinkList shrink ts)

deriving instance Generic Literal
instance Arbitrary Literal where
  arbitrary = genericArbitraryRec (1 % 1 % 1 % ())
  shrink = \case
    Constant _     -> []
    Predicate p ts -> Predicate p <$> shrinkList shrink ts
    Equality _ _   -> []

deriving instance Generic Quantifier
instance Arbitrary Quantifier where
  arbitrary = genericArbitraryU

deriving instance Generic Connective
instance Arbitrary Connective where
  arbitrary = genericArbitraryU

deriving instance Generic Formula
instance Arbitrary Formula where
  arbitrary = genericArbitraryRec (3 % 2 % 1 % 2 % ())
  shrink = \case
    Atomic l         -> Atomic <$> shrink l
    Negate f         -> f : (Negate <$> shrink f)
    Connected f c g  -> f : g : (Connected <$> shrink f <*> pure c <*> shrink g)
    Quantified q v f -> f : (Quantified q v <$> shrink f)


-- * Theorems

deriving instance Generic Theorem
instance Arbitrary Theorem where
  arbitrary = genericArbitraryU
  shrink (Theorem as c) = Theorem <$> shrinkList shrink as <*> shrink c


-- * Proofs

deriving instance Generic (Inference f)
instance Arbitrary f => Arbitrary (Inference f) where
  arbitrary = genericArbitraryU

deriving instance Generic (Derivation l)
instance Arbitrary l => Arbitrary (Derivation l) where
  arbitrary = genericArbitraryU
  shrink (Derivation i f) = Derivation i <$> shrink f

deriving instance Generic (Refutation l)
instance Arbitrary l => Arbitrary (Refutation l) where
  arbitrary = genericArbitraryU
  shrink (Refutation i ds) = Refutation i <$> shrinkList shrink ds
