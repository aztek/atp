{-# LANGUAGE GeneralizedNewtypeDeriving #-}

{-|
Module       : ATP.FirstOrder.Alpha
Description  : Monads and monad transformers for computations with free and
               bound variables.
Copyright    : (c) Evgenii Kotelnikov, 2019-2021
License      : GPL-3
Maintainer   : evgeny.kotelnikov@gmail.com
Stability    : experimental
-}

module ATP.FirstOrder.Alpha (
  AlphaT,
  evalAlphaT,
  Alpha,
  evalAlpha,
  lookup,
  scope,
  enter,
  share,
  MonadAlpha(..)
) where

import Prelude hiding (lookup)
import Control.Applicative ((<|>))
import Control.Monad.Trans (MonadTrans(..))
import Control.Monad.Reader (MonadReader(..), ReaderT(..), asks)
import Control.Monad.State (MonadState(..), StateT(..), modify, gets)
import Data.Functor.Identity (Identity(..))
import qualified Data.List as L (lookup)
import qualified Data.Map as M (empty, lookup, insert, elems)
import Data.Map (Map)

import ATP.FirstOrder.Core


-- | The stack of renamings for the bound variables in the expression.
type Stack = [(Var, Var)]

-- | The rename mapping for the free variables in the expression.
type Global = Map Var Var

-- | The monad transformer that adds to the given monad @m@ the ability to track
-- a renaming of free and bound variables in a first-order expression.
newtype AlphaT m a = AlphaT (ReaderT Stack (StateT Global m) a)
  deriving (Functor, Applicative, Monad, MonadReader Stack, MonadState Global)

instance MonadTrans AlphaT where
  lift = AlphaT . lift . lift

runAlphaT :: AlphaT m a -> m (a, Global)
runAlphaT (AlphaT r) = runStateT (runReaderT r []) M.empty

-- | Evaluate an alpha computation and return the final value,
-- discarding the global scope.
evalAlphaT :: Monad m => AlphaT m a -> m a
evalAlphaT = fmap fst . runAlphaT


-- | The alpha monad parametrized by the type @a@ of the return value.
type Alpha a = AlphaT Identity a

-- | Evaluate an 'Alpha' computation and return the final value,
-- discarding the final variable renaming.
evalAlpha :: Alpha a -> a
evalAlpha = runIdentity . evalAlphaT


-- | Lookup a variable, first in the stack of bound variables,
-- then in the global scope.
lookup :: Monad m => Var -> AlphaT m (Maybe Var)
lookup v = do
  bv <- asks (L.lookup v)
  fv <- gets (M.lookup v)
  return (bv <|> fv)

-- | Read the set of free and bound variables of the given 'AlphaT' computation.
scope :: Monad m => AlphaT m [Var]
scope = do
  bv <- asks (fmap snd)
  fv <- gets M.elems
  return (bv ++ fv)

-- | Run a computation inside 'AlphaT' with the variable renaming.
enter :: Monad m => Var -> Var -> AlphaT m a -> AlphaT m a
enter v w = local ((v,w):)

-- | Update the global scope with a variable renaming.
share :: Monad m => Var -> Var -> AlphaT m ()
share v w = modify (M.insert v w)


-- | A helper monad for computations on free and bound occurrences of variables.
class Monad m => MonadAlpha m where
  -- | A monadic action to perform on a variable under a quantifier.
  binding :: Var -> AlphaT m Var

  -- | A monadic action to perform on a variable occurrence.
  occurrence :: Var -> AlphaT m Var
