{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE DeriveGeneric #-}
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

module QuickCheckSpec.Generators () where

#if !MIN_VERSION_base(4, 8, 0)
import Control.Applicative (pure, (<$>), (<*>))
#endif

import GHC.Generics (Generic)
import Generic.Random (genericArbitraryU, genericArbitraryRec, (%))

import Data.Text (Text, pack)
import Test.QuickCheck (Arbitrary(..), shrinkList, listOf1, choose)

import ATP.FOL


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
