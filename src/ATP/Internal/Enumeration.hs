{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

{-|
Module       : ATP.Internal.Enumeration
Description  : The helper Enumeration monad used to describe computations with
               renaming values with consequtive numbers.
Copyright    : (c) Evgenii Kotelnikov, 2019-2020
License      : GPL-3
Maintainer   : evgeny.kotelnikov@gmail.com
Stability    : experimental
-}

module ATP.Internal.Enumeration (
  Enumeration,
  evalEnumeration,
  fresh,
  enumerate,
  alias
) where

import Control.Monad.State (MonadState, State, evalState, gets, modify)
import Data.Map (Map)
import qualified Data.Map as M (empty, lookup, insert)


newtype Enumeration a s = Enumeration (State (Integer, Map a Integer) s)
  deriving (Functor, Applicative, Monad, MonadState (Integer, Map a Integer))

evalEnumeration :: Enumeration a e -> e
evalEnumeration (Enumeration s) = evalState s (1, M.empty)

fresh :: Enumeration a Integer
fresh = do
  i <- gets fst
  modify $ \(j, m) -> (j + 1, m)
  return i

enumerate :: Ord a => a -> Enumeration a Integer
enumerate v = gets (M.lookup v . snd) >>= \case
  Just w -> return w
  Nothing -> do
    i <- fresh
    modify $ fmap (M.insert v i)
    return i

alias :: Ord a => a -> a -> Enumeration a ()
alias original synonym = modify . fmap . M.insert synonym =<< enumerate original
