{-# LANGUAGE CPP #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE FlexibleInstances #-}

{-|
Module       : ATP.FirstOrder.Occurrence
Description  : Occurrences of variables in first-order expressions.
Copyright    : (c) Evgenii Kotelnikov, 2019-2020
License      : GPL-3
Maintainer   : evgeny.kotelnikov@gmail.com
Stability    : experimental
-}

module ATP.FirstOrder.Occurrence (
  -- * Occurrence
  FirstOrder(vars, free, bound, occursIn, freeIn, boundIn, (~=), alpha),
  closed,
  close,
  unprefix
) where

import Prelude hiding (lookup)
import Control.Monad (liftM2, zipWithM, when)
import Data.Function (on)
#if !MIN_VERSION_base(4, 11, 0)
import Data.Semigroup (Semigroup(..))
#endif
import qualified Data.Set as S (insert, delete, member, null, singleton)
import Data.Set (Set)

import ATP.FirstOrder.Core
import ATP.FirstOrder.Alpha

-- $setup
-- >>> :load QuickCheckSpec.Generators


-- * Occurrence

infix 5 ~=

-- | A class of first-order expressions, i.e. expressions that might contain
-- variables. @'Formula'@s, @'Literal'@s and @'Term'@s are first-order expressions.
--
-- A variable can occur both as free and bound, therefore
-- @'free' e@ and @'bound' e@ are not necessarily disjoint and
-- @v `freeIn` e@ and @v `boundIn` e@ are not necessarily musually exclusive.
--
-- @'vars'@, @'free'@ and @'bound'@ are connected by the following property.
--
-- > free e <> bound e == vars e
--
-- @'occursIn'@, @'freeIn'@ and @'boundIn'@ are connected by the following property.
--
-- > v `freeIn` e || v `boundIn` e == v `occursIn` e
--
class FirstOrder e where
  -- | The set of all variables that occur anywhere in the given expression.
  vars :: e -> Set Var

  -- | The set of variables that occur freely in the given expression,
  -- i.e. are not bound by any quantifier inside the expression.
  free :: e -> Set Var

  -- | The set of variables that occur bound in the given expression,
  -- i.e. are bound by a quantifier inside the expression.
  bound :: e -> Set Var

  -- | Check whether the given variable occurs anywhere in the given expression.
  occursIn :: Var -> e -> Bool
  v `occursIn` e = v `S.member` vars e

  -- | Check whether the given variable occurs freely anywhere in the given expression.
  freeIn :: Var -> e -> Bool
  v `freeIn` e = v `S.member` free e

  -- | Check whether the given variable occurs bound anywhere in the given expression.
  boundIn :: Var -> e -> Bool
  v `boundIn` e = v `S.member` bound e

  -- | Check whether the given expression is ground, i.e. does not contain
  -- any variables.
  --
  -- Note that /ground formula/ is sometimes understood as /formula that does/
  -- /not contain any free variables/. In this library such formulas are called
  -- @'closed'@.
  ground :: e -> Bool
  ground = S.null . vars

  -- | Check whether two given expressions are alpha-equivalent, that is
  -- equivalent up to renaming of variables.
  --
  -- '(~=)' is an equivalence relation.
  --
  -- __Symmetry__
  --
  -- > e ~= e
  --
  -- __Reflexivity__
  --
  -- > a ~= b == b ~= a
  --
  -- __Transitivity__
  --
  -- > a ~= b && b ~= c ==> a ~= c
  --
  (~=) :: e -> e -> Bool
  a ~= b = evalAlpha (a ?= b)

  -- | A helper function calculating alpha-equivalence using the 'Alpha' monad stack.
  (?=) :: e -> e -> Alpha Bool

  alpha :: AlphaMonad m => e -> AlphaT m e

instance FirstOrder LogicalExpression where
  vars = \case
    Clause  c -> vars c
    Formula f -> vars f

  free = \case
    Clause  c -> free c
    Formula f -> free f

  bound = \case
    Clause  c -> bound c
    Formula f -> bound f

  occursIn v = \case
    Clause  c -> occursIn v c
    Formula f -> occursIn v f

  freeIn v = \case
    Clause  c -> freeIn v c
    Formula f -> freeIn v f

  boundIn v = \case
    Clause  c -> boundIn v c
    Formula f -> boundIn v f

  ground = \case
    Clause  c -> ground c
    Formula f -> ground f

  Clause  c ?= Clause  c' = c ?= c'
  Formula f ?= Formula f' = f ?= f'
  _         ?= _          = return False

  alpha = \case
    Clause  c -> Clause  <$> alpha c
    Formula f -> Formula <$> alpha f

instance FirstOrder Formula where
  vars = \case
    Atomic l         -> vars l
    Negate f         -> vars f
    Connected  _ f g -> vars f <> vars g
    Quantified _ _ f -> vars f

  free = \case
    Atomic l         -> free l
    Negate f         -> free f
    Connected  _ f g -> free f <> free g
    Quantified _ v f -> S.delete v (free f)

  bound = \case
    Atomic{}         -> mempty
    Negate f         -> bound f
    Connected  _ f g -> bound f <> bound g
    Quantified _ v f -> if v `freeIn` f then S.insert v (bound f) else bound f

  Atomic l ?= Atomic l' = l ?= l'
  Negate f ?= Negate f' = f ?= f'
  Connected  c f g ?= Connected  c' f' g' | c == c' = liftM2 (&&) (f ?= f') (g ?= g')
  Quantified q v f ?= Quantified q' v' f' | q == q' = enter v v' (f ?= f')
  _ ?= _ = return False

  alpha = \case
    Atomic l -> Atomic <$> alpha l
    Negate f -> Negate <$> alpha f
    Connected  c f g -> Connected c <$> alpha f <*> alpha g
    Quantified q v f -> do
      v' <- binding v
      f' <- enter v v' (alpha f)
      return (Quantified q v' f')

instance FirstOrder Clause where
  vars = vars . unClause
  free = vars
  bound _ = mempty
  (~=) = (~=) `on` unClause
  (?=) = (?=) `on` unClause
  alpha = fmap Literals . traverse alpha . unClause

instance FirstOrder e => FirstOrder (Signed e) where
  vars  = vars  . unsign
  free  = free  . unsign
  bound = bound . unsign

  occursIn v = occursIn v . unsign
  freeIn   v = freeIn   v . unsign
  boundIn  v = boundIn  v . unsign

  ground = ground . unsign

  (~=) = (~=) `on` unsign
  (?=) = (?=) `on` unsign

  alpha = traverse alpha

instance FirstOrder Literal where
  vars = \case
    Constant{}     -> mempty
    Predicate _ ts -> vars ts
    Equality a b   -> vars a <> vars b

  free = vars
  bound _ = mempty

  Constant  b    ?= Constant  b'     = return (b == b')
  Predicate p ts ?= Predicate p' ts' | p == p' = ts ?= ts'
  Equality  a b  ?= Equality  a' b'  = liftM2 (&&) (a ?= a') (b ?= b')
  _ ?= _ = return False

  alpha = \case
    Constant b     -> return (Constant b)
    Predicate p ts -> Predicate p <$> traverse alpha ts
    Equality a b   -> Equality <$> alpha a <*> alpha b

instance FirstOrder Term where
  vars = \case
    Variable v    -> vars v
    Function _ ts -> vars ts

  free = vars
  bound _ = mempty

  Variable v    ?= Variable v'     = v ?= v'
  Function f ts ?= Function f' ts' | f == f' = ts ?= ts'
  _ ?= _ = return False

  alpha = \case
    Function f ts -> Function f <$> traverse alpha ts
    Variable v    -> Variable   <$> alpha v

instance FirstOrder Var where
  vars = S.singleton
  free = vars
  bound _ = mempty

  v ?= v' = lookup v >>= \case
    Just w' -> return (w' == v')
    Nothing -> do
      vs <- scope
      let f = v' `notElem` vs
      when f (share v v')
      return f

  alpha v = lookup v >>= \case
    Just v' -> occurrence v'
    Nothing -> do { v' <- binding v; share v v'; return v' }

instance FirstOrder e => FirstOrder [e] where
  vars = mconcat . fmap vars
  free = vars
  bound = mempty

  es ?= es' | length es == length es' = and <$> zipWithM (?=) es es'
  _  ?= _   = return False

  alpha = traverse alpha

-- | Check whether the given formula is closed, i.e. does not contain any free
-- variables.
closed :: Formula -> Bool
closed = S.null . free

-- | Make any given formula closed by adding a top-level universal quantifier
-- for each of its free variables.
--
-- @'close'@ and @'unprefix'@ are connected by the following property.
--
-- prop> unprefix (close f) === f
--
close :: Formula -> Formula
close f = foldl (flip $ Quantified Forall) f (free f)

-- | Remove the top-level quantifiers.
--
-- >>> unprefix (Quantified Forall 1 (Quantified Exists 2 (Atomic (Equality (Variable 1) (Variable 2)))))
-- Atomic (Equality (Variable 1) (Variable 2))
--
unprefix :: Formula -> Formula
unprefix = \case
  Quantified _ _ f -> unprefix f
  f -> f
