{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

{-|
Module       : ATP.Internal.Enumeration
Description  : The helper Enumeration monad used to describe computations that
               carry on a renaming of values to consecutive numbers.
Copyright    : (c) Evgenii Kotelnikov, 2019-2020
License      : GPL-3
Maintainer   : evgeny.kotelnikov@gmail.com
Stability    : experimental
-}

module ATP.Internal.Enumeration (
  EnumerationT(..),
  evalEnumerationT,
  Enumeration,
  evalEnumeration,
  next,
  enumerate,
  alias
) where

import Control.Monad.State (MonadTrans, MonadState, StateT, evalStateT, gets, modify)
import Data.Functor.Identity (Identity(..))
import Data.Map (Map)
import qualified Data.Map as M (empty, lookup, insert)


newtype EnumerationT a m s = EnumerationT {
  runEnumerationT :: StateT (Integer, Map a Integer) m s
} deriving (Functor, Applicative, Monad, MonadTrans, MonadState (Integer, Map a Integer))

evalEnumerationT :: Monad m => EnumerationT a m e -> m e
evalEnumerationT e = evalStateT (runEnumerationT e) (1, M.empty)

type Enumeration a = EnumerationT a Identity

evalEnumeration :: Enumeration a e -> e
evalEnumeration = runIdentity . evalEnumerationT

next :: Monad m => EnumerationT a m Integer
next = do
  i <- gets fst
  modify $ \(j, m) -> (j + 1, m)
  return i

enumerate :: (Ord a, Monad m) => a -> EnumerationT a m Integer
enumerate v = gets (M.lookup v . snd) >>= \case
  Just w -> return w
  Nothing -> do
    i <- next
    modify $ fmap (M.insert v i)
    return i

alias :: (Ord a, Monad m) => a -> a -> EnumerationT a m ()
alias a b = gets (\(_, m) -> (M.lookup a m, M.lookup b m)) >>= \case
  (Just{},  Just{})  -> error "alias"
  (Just i,  Nothing) -> modify $ fmap (M.insert b i)
  (Nothing, Just i)  -> modify $ fmap (M.insert a i)
  (Nothing, Nothing) -> do
    i <- next
    modify $ fmap (M.insert a i)
    modify $ fmap (M.insert b i)
