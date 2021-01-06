{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleInstances #-}

{-|
Module       : Property.Modifiers.AlphaEquivalent
Description  : QuickCheck generators of alpha-equivalent and alpha-inequivalent
               first-order expressions.
Copyright    : (c) Evgenii Kotelnikov, 2019-2021
License      : GPL-3
Maintainer   : evgeny.kotelnikov@gmail.com
Stability    : experimental
-}

module Property.Modifiers.AlphaEquivalent (
  genAlphaEquivalent,
  genAlphaInequivalent
) where

import Control.Monad.Trans (lift)

import Test.QuickCheck (Arbitrary(..), Gen, suchThat, elements)

import ATP.FOL


-- * Alpha-equivalent first-order expressions.

genAlphaEquivalent :: FirstOrder e => e -> Gen e
genAlphaEquivalent = getAlphaEquivalence . evalAlphaT . alpha

newtype AlphaEquivalence m a = AlphaEquivalence { getAlphaEquivalence :: m a }
  deriving (Functor, Applicative, Monad)

instance MonadAlpha (AlphaEquivalence Gen) where
  binding _  = fresh
  occurrence = return


-- * Alpha-inequivalent first-order expressions.

genAlphaInequivalent :: FirstOrder e => e -> Gen e
genAlphaInequivalent = getAlphaInequivalence . evalAlphaT . alpha

newtype AlphaInequivalence m a = AlphaInequivalence { getAlphaInequivalence :: m a }
  deriving (Functor, Applicative, Monad)

instance MonadAlpha (AlphaInequivalence Gen) where
  binding _  = stale
  occurrence = anythingBut


-- * Helper functions

fresh :: AlphaT (AlphaEquivalence Gen) Var
fresh = do
  vs <- scope
  lift . AlphaEquivalence $ arbitrary `suchThat` (`notElem` vs)

stale :: AlphaT (AlphaInequivalence Gen) Var
stale = do
  vs <- scope
  lift . AlphaInequivalence $ if null vs then arbitrary else elements vs

anythingBut :: Var -> AlphaT (AlphaInequivalence Gen) Var
anythingBut v = lift . AlphaInequivalence $ arbitrary `suchThat` (/= v)
