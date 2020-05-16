{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE CPP #-}

{-|
Module       : QuickCheckSpec.Generators.FOL
Description  : QuickCheck generators of first-order formulas, theorems and proofs.
Copyright    : (c) Evgenii Kotelnikov, 2020
License      : GPL-3
Maintainer   : evgeny.kotelnikov@gmail.com
Stability    : experimental
-}

module QuickCheckSpec.Generators.FOL () where

import GHC.Generics (Generic)
import Generic.Random (genericArbitraryU, genericArbitraryRec, (%), uniform)

import Data.Text (Text, pack)
import Test.QuickCheck (Arbitrary(..), listOf1, choose, genericShrink)

import ATP.FOL


-- * Formulas

instance Arbitrary Text where
  arbitrary = pack <$> listOf1 (choose ('a', 'z'))

deriving instance Generic Term
instance Arbitrary Term where
  arbitrary = genericArbitraryRec uniform
  shrink = genericShrink

deriving instance Generic Literal
instance Arbitrary Literal where
  arbitrary = genericArbitraryRec uniform
  shrink = genericShrink

deriving instance Generic Sign
instance Arbitrary Sign where
  arbitrary = genericArbitraryU

deriving instance Generic (Signed a)
instance Arbitrary a => Arbitrary (Signed a) where
  arbitrary = genericArbitraryU
  shrink = genericShrink

deriving instance Generic Clause
instance Arbitrary Clause where
  arbitrary = genericArbitraryU
  shrink = genericShrink

deriving instance Generic Quantifier
instance Arbitrary Quantifier where
  arbitrary = genericArbitraryU

deriving instance Generic Connective
instance Arbitrary Connective where
  arbitrary = genericArbitraryU

deriving instance Generic Formula
instance Arbitrary Formula where
  arbitrary = genericArbitraryRec (3 % 2 % 1 % 2 % ())
  shrink = genericShrink

deriving instance Generic LogicalExpression
instance Arbitrary LogicalExpression where
  arbitrary = genericArbitraryU
  shrink = genericShrink


-- * Theorems

deriving instance Generic Theorem
instance Arbitrary Theorem where
  arbitrary = genericArbitraryU
  shrink = genericShrink


-- * Proofs

deriving instance Generic (Inference f)
instance Arbitrary f => Arbitrary (Inference f) where
  arbitrary = genericArbitraryU

deriving instance Generic (Derivation l)
instance Arbitrary l => Arbitrary (Derivation l) where
  arbitrary = genericArbitraryU
  shrink = genericShrink

deriving instance Generic (Refutation l)
instance Arbitrary l => Arbitrary (Refutation l) where
  arbitrary = genericArbitraryU
  shrink = genericShrink
