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

import Data.Text (pack)
import Test.QuickCheck (Arbitrary(..), listOf1, choose, genericShrink)

import ATP.FOL


-- * Formulas

deriving instance Generic FunctionSymbol
instance Arbitrary FunctionSymbol where
  arbitrary = FunctionSymbol . pack <$> listOf1 (choose ('a', 'z'))

deriving instance Generic Term
instance Arbitrary Term where
  arbitrary = genericArbitraryRec uniform
  shrink = genericShrink

deriving instance Generic PredicateSymbol
instance Arbitrary PredicateSymbol where
  arbitrary = PredicateSymbol . pack <$> listOf1 (choose ('A', 'Z'))

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


-- * Problems

deriving instance Generic ClauseSet
instance Arbitrary ClauseSet where
  arbitrary = genericArbitraryU
  shrink = genericShrink

deriving instance Generic Theorem
instance Arbitrary Theorem where
  arbitrary = genericArbitraryU
  shrink = genericShrink


-- * Proofs

instance Arbitrary RuleName where
  arbitrary = RuleName . pack <$> listOf1 (choose ('a', 'z'))

deriving instance Generic (Rule f)
instance Arbitrary f => Arbitrary (Rule f) where
  arbitrary = genericArbitraryU

deriving instance Generic (Inference f)
instance Arbitrary f => Arbitrary (Inference f) where
  arbitrary = genericArbitraryU

deriving instance Generic (Contradiction f)
instance Arbitrary f => Arbitrary (Contradiction f) where
  arbitrary = genericArbitraryU

deriving instance Generic (Sequent f)
instance Arbitrary f => Arbitrary (Sequent f) where
  arbitrary = genericArbitraryU

deriving instance Generic (Derivation f)
instance (Ord f, Arbitrary f) => Arbitrary (Derivation f) where
  arbitrary = genericArbitraryU
  shrink = genericShrink

deriving instance Generic (Refutation f)
instance (Ord f, Arbitrary f) => Arbitrary (Refutation f) where
  arbitrary = genericArbitraryU
  shrink = genericShrink
