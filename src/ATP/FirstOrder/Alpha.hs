{-# LANGUAGE GeneralizedNewtypeDeriving #-}

{-|
Module       : ATP.FirstOrder.Alpha
Description  : Monads and monad transformers for computations with free and
               bound variables.
Copyright    : (c) Evgenii Kotelnikov, 2019-2020
License      : GPL-3
Maintainer   : evgeny.kotelnikov@gmail.com
Stability    : experimental
-}

module ATP.FirstOrder.Alpha (
  AlphaT(..),
  runAlphaT,
  evalAlphaT,
  execAlphaT,

  Alpha,
  runAlpha,
  evalAlpha,
  execAlpha,

  lookup,
  scope,
  enter,
  share,

  AlphaMonad(..)
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


type Stack = [(Var, Var)]
type Global = Map Var Var

newtype AlphaT m a = AlphaT (ReaderT Stack (StateT Global m) a)
  deriving (Functor, Applicative, Monad, MonadReader Stack, MonadState Global)

instance MonadTrans AlphaT where
  lift = AlphaT . lift . lift

runAlphaT :: AlphaT m a -> m (a, Global)
runAlphaT (AlphaT r) = runStateT (runReaderT r []) M.empty

evalAlphaT :: Monad m => AlphaT m a -> m a
evalAlphaT = fmap fst . runAlphaT

execAlphaT :: Monad m => AlphaT m a -> m Global
execAlphaT = fmap snd . runAlphaT


type Alpha a = AlphaT Identity a

runAlpha :: Alpha a -> (a, Global)
runAlpha = runIdentity . runAlphaT

evalAlpha :: Alpha a -> a
evalAlpha = runIdentity . evalAlphaT

execAlpha :: Alpha a -> Global
execAlpha = runIdentity . execAlphaT


-- | Lookup a variable, first in the stack of bound variables,
-- then in the global scope.
lookup :: Monad m => Var -> AlphaT m (Maybe Var)
lookup v = do
  bv <- asks (L.lookup v)
  fv <- gets (M.lookup v)
  return (bv <|> fv)

scope :: Monad m => AlphaT m [Var]
scope = do
  bv <- asks (fmap snd)
  fv <- gets M.elems
  return (bv ++ fv)

enter :: Monad m => Var -> Var -> AlphaT m a -> AlphaT m a
enter v w = local ((v,w):)

-- | Update the global scope with a variable renaming.
share :: Monad m => Var -> Var -> AlphaT m ()
share v w = modify (M.insert v w)


-- | A helper monad for computations on free and bound occurrences of variables.
class Monad m => AlphaMonad m where
  -- | A monadic action to perform on a variable under a quantified.
  binding :: Var -> AlphaT m Var

  -- | A monadic action to perform on a variable occuring in a term.
  occurrence :: Var -> AlphaT m Var
