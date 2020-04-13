{-# LANGUAGE LambdaCase #-}

{-|
Module       : ATP.FOL.Occurrence
Description  : Occurrences of variables in first-order expressions.
Copyright    : (c) Evgenii Kotelnikov, 2019-2020
License      : GPL-3
Maintainer   : evgeny.kotelnikov@gmail.com
Stability    : experimental
-}

module ATP.FOL.Occurrence (
  -- * Occurrence
  FirstOrder(..),
  closed,
  close,
  unprefix
) where

import Control.Monad (foldM, zipWithM, liftM2, guard)
import Data.Function (on)
import Data.Functor (($>))
import qualified Data.Map as M
import Data.Map (Map)
import Data.Maybe (isJust)
import qualified Data.Set as S
import Data.Set (Set)

import ATP.FOL.Formula

-- $setup
-- >>> :load QuickCheckSpec.Generators


-- * Occurrence

-- | Renaming is an injective mapping of variables.
type Renaming = Map Var Var

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
-- > free e `S.union` bound e == vars e
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

  -- | @'alpha' a b@ returns 'Nothing' if 'a' cannot be alpha converted to 'b'
  -- and 'Just r', where 'r' is a renaming, otherwise.
  alpha :: e -> e -> Maybe Renaming

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
  a ~= b = isJust (alpha a b)

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

  alpha (Clause  c) (Clause  c') = alpha c c'
  alpha (Formula f) (Formula f') = alpha f f'
  alpha _           _            = Nothing

insertRenaming :: Renaming -> (Var, Var) -> Maybe Renaming
insertRenaming r (v, v') = guard p $> M.insert v v' r
  where p = maybe (v' `notElem` M.elems r) (== v') (M.lookup v r)

mergeRenamings :: Renaming -> Renaming -> Maybe Renaming
mergeRenamings r = foldM insertRenaming r . M.toList

instance FirstOrder Formula where
  vars = \case
    Atomic l         -> vars l
    Negate f         -> vars f
    Connected  _ f g -> vars f `S.union` vars g
    Quantified _ _ f -> vars f

  free = \case
    Atomic l         -> vars l
    Negate f         -> free f
    Connected  _ f g -> free f `S.union` free g
    Quantified _ v f -> S.delete v (free f)

  bound = \case
    Atomic{}         -> S.empty
    Negate f         -> bound f
    Connected  _ f g -> bound f `S.union` bound g
    Quantified _ v f -> if v `freeIn` f then S.insert v (bound f) else bound f

  alpha (Atomic l) (Atomic l') = alpha l l'
  alpha (Negate f) (Negate f') = alpha f f'
  alpha (Connected c f g) (Connected c' f' g') | c == c' =
    uncurry mergeRenamings =<< liftM2 (,) (alpha f f') (alpha g g')
  alpha (Quantified q v f) (Quantified q' v' f') | q == q' =
    uncurry mergeRenamings =<< liftM2 (,) (alpha f f') (Just $ M.singleton v v')
  alpha _ _ = Nothing

instance FirstOrder Clause where
  vars = S.unions . fmap vars . unClause

  free = vars

  bound _ = S.empty

  alpha (Literals ls) (Literals ls') | length ls == length ls' =
    foldM mergeRenamings M.empty =<< zipWithM alpha ls ls'
  alpha _ _ = Nothing

instance FirstOrder e => FirstOrder (Signed e) where
  vars  = vars  . unsign
  free  = free  . unsign
  bound = bound . unsign

  occursIn v = occursIn v . unsign
  freeIn   v = freeIn   v . unsign
  boundIn  v = boundIn  v . unsign

  ground = ground . unsign

  alpha = alpha `on` unsign
  (~=) = (~=) `on` unsign

instance FirstOrder Literal where
  vars = \case
    Constant{}     -> S.empty
    Predicate _ ts -> S.unions (fmap vars ts)
    Equality a b   -> vars a `S.union` vars b

  free = vars

  bound _ = S.empty

  alpha (Constant b) (Constant b') | b == b' = Just M.empty
  alpha (Predicate p ts) (Predicate p' ts') | p == p', length ts == length ts' =
    foldM mergeRenamings M.empty =<< zipWithM alpha ts ts'
  alpha (Equality a b) (Equality a' b') =
    uncurry mergeRenamings =<< liftM2 (,) (alpha a a') (alpha b b')
  alpha _ _ = Nothing

instance FirstOrder Term where
  vars = \case
    Variable v    -> S.singleton v
    Function _ ts -> S.unions (fmap vars ts)

  free = vars

  bound _ = S.empty

  alpha (Variable v) (Variable v') = Just (M.singleton v v')
  alpha (Function f ts) (Function f' ts') | f == f', length ts == length ts' =
    foldM mergeRenamings M.empty =<< zipWithM alpha ts ts'
  alpha _ _ = Nothing

-- | Check whether the given formula is closed, i.e. does not contain any free
-- variables.
closed :: Formula -> Bool
closed = S.null . free

-- | Make any given formula closed by adding a top-level universal quantifier
-- for each of its free variables.
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
