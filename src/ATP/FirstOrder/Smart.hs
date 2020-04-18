{-# LANGUAGE Trustworthy #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE FlexibleInstances #-}

{-|
Module       : ATP.FirstOrder.Smart
Description  : Smart constructors for terms and formulas in first-order logic.
Copyright    : (c) Evgenii Kotelnikov, 2019-2020
License      : GPL-3
Maintainer   : evgeny.kotelnikov@gmail.com
Stability    : experimental
-}

module ATP.FirstOrder.Smart (
  -- * Smart constructors
  unitClause,
  signed,
  (\./),
  clause,
  (===),
  (=/=),
  neg,
  (\/),
  (/\),
  (==>),
  (<=>),
  (<~>),
  Binder(..),
  forall,
  exists,

  -- * Monoids in first-order logic
  ClauseUnion(..),
  clauseUnion,
  Conjunction(..),
  conjunction,
  Disjunction(..),
  disjunction,
  Equivalence(..),
  equivalence,
  Inequivalence(..),
  inequivalence
) where

import Data.Coerce (coerce)
import qualified Data.Foldable as Foldable (toList)
#if !MIN_VERSION_base(4, 11, 0)
import Data.Semigroup (Semigroup(..))
#endif

import ATP.FirstOrder.Core

-- $setup
-- >>> :set -XOverloadedStrings
-- >>> :load QuickCheckSpec.Generators
-- >>> let eq = binaryPredicate "eq"


-- * Smart constructors

infix  8 ===
infix  8 =/=
infixl 7 /\ --
infixl 6 \/
infixl 6 \./
infix  5 ==>
infixl 5 <=>
infixl 5 <~>

-- | A smart constructor for a signed literal.
signed :: Sign -> Literal -> Signed Literal
signed Negative (Constant b) = Signed Positive (Constant (not b))
signed s l = Signed s l

-- | A smart constructor for a unit clause.
unitClause :: Signed Literal -> Clause
unitClause (Signed s l) = case signed s l of
  FalsumLiteral -> EmptyClause
  sl -> UnitClause sl

-- | Smart union of two clauses.
-- ('\./') has the following properties.
--
-- __Associativity__
--
-- prop> (f \./ g) \./ h == f \./ (g \./ h)
--
-- __Left identity__
--
-- prop> EmptyClause \./ c == c
--
-- __Right identity__
--
-- prop> c \./ EmptyClause == c
--
-- __Left zero__
--
-- prop> TautologyClause \./ c == TautologyClause
--
-- __Right zero__
--
-- prop> c \./ TautologyClause == TautologyClause
--
(\./) :: Clause -> Clause -> Clause
EmptyClause \./ c = c
c \./ EmptyClause = c
TautologyClause \./ _ = TautologyClause
_ \./ TautologyClause = TautologyClause
Literals cs \./ Literals ss = Literals (cs <> ss)

-- | A smart contructor for a clause.
-- 'clause' eliminates negated boolean constants, falsums and redundant tautologies.
clause :: Foldable f => f (Signed Literal) -> Clause
clause = clauseUnion . fmap unitClause . Foldable.toList

-- | A smart constructor for equality.
(===) :: Term -> Term -> Formula
a === b = Atomic (Equality a b)

-- | A smart constructor for inequality.
(=/=) :: Term -> Term -> Formula
a =/= b = Negate (a === b)

-- | A smart constructor for negation.
neg :: Formula -> Formula
neg = \case
  Tautology -> Falsum
  Falsum    -> Tautology
  Negate f  -> f
  f         -> Negate f

-- | A smart contructor for the 'And' connective.
-- ('/\') has the following properties.
--
-- __Associativity__
--
-- prop> (f /\ g) /\ h == f /\ (g /\ h)
--
-- __Left identity__
--
-- prop> Tautology /\ g == g
--
-- __Right identity__
--
-- prop> f /\ Tautology == f
--
(/\) :: Formula -> Formula -> Formula
Falsum    /\ _ = Falsum
Tautology /\ g = g
_ /\ Falsum    = Falsum
f /\ Tautology = f
Connected And f g /\ h = f /\ (g /\ h)
f /\ g = Connected And f g

-- | A smart constructor for the 'Or' connective.
-- ('\/') has the following properties.
--
-- __Associativity__
--
-- prop> (f \/ g) \/ h == f \/ (g \/ h)
--
-- __Left identity__
--
-- prop> Falsum \/ g == g
--
-- __Right identity__
--
-- prop> f \/ Falsum == f
--
(\/) :: Formula -> Formula -> Formula
Tautology \/ _ = Tautology
Falsum    \/ g = g
_ \/ Tautology = Tautology
f \/ Falsum    = f
Connected Or f g \/ h = f \/ (g \/ h)
f \/ g = Connected Or f g

-- | A smart constructor for the 'Implies' connective.
(==>) :: Formula -> Formula -> Formula
Tautology ==> g = g
Falsum    ==> _ = Tautology
_ ==> Tautology = Tautology
f ==> Falsum    = neg f
f ==> g = Connected Implies f g

-- | A smart constructor for the 'Equivalent' connective.
-- ('<=>') has the following properties.
--
-- __Associativity__
--
-- prop> (f <=> g) <=> h == f <=> (g <=> h)
--
-- __Left identity__
--
-- prop> Tautology <=> g == g
--
-- __Right identity__
--
-- prop> f <=> Tautology == f
--
(<=>) :: Formula -> Formula -> Formula
Tautology <=> g = g
f <=> Tautology = f
Connected Equivalent f g <=> h = f <=> (g <=> h)
f <=> g = Connected Equivalent f g

-- | A smart constructor for the 'Xor' connective.
-- ('<~>') has the following properties.
--
-- __Associativity__
--
-- prop> (f <~> g) <~> h == f <~> (g <~> h)
--
-- __Left identity__
--
-- prop> Falsum <~> g == g
--
-- __Right identity__
--
-- prop> f <~> Falsum == f
--
(<~>) :: Formula -> Formula -> Formula
Falsum <~> g = g
f <~> Falsum = f
Connected Xor f g <~> h = f <~> (g <~> h)
f <~> g = Connected Xor f g

-- | A class of binders for quantified variables.
--
-- This class and its instances provides machinery for using polyvariadic
-- functions as higher-order abstract syntax for bindings of
-- quantified variables.
--
-- > eq = binaryPredicate "eq"
--
-- >>> quantified Forall $ \x -> x `eq` x
-- Quantified Forall 1 (Atomic (Predicate "eq" [Variable 1,Variable 1]))
--
-- >>> quantified Forall $ \x y -> x `eq` y ==> y `eq` x
-- Quantified Forall 2 (Quantified Forall 1 (Connected Implies (Atomic (Predicate "eq" [Variable 2,Variable 1])) (Atomic (Predicate "eq" [Variable 1,Variable 2]))))
class Binder b where
  -- | A smart constructor for quantified formulas.
  quantified :: Quantifier -> b -> Formula

-- | The degenerate instance - no variable is bound.
instance Binder Formula where
  quantified _ f = f

-- | The trivial instance - binder of the varible with the given name.
instance Binder (Var, Formula) where
  quantified q (v, f) = case f of
    Tautology -> f
    Falsum    -> f
    _         -> Quantified q v f

-- | The recursive instance for polyvariadic bindings of quantified variables.
-- This is a generalized version of
-- <https://emilaxelsson.github.io/documents/axelsson2013using.pdf>.
instance Binder b => Binder (Term -> b) where
  quantified q b = quantified q (v, f)
    where
      f = quantified q (b (Variable v))
      v = 1 + maxvar f

      maxvar :: Formula -> Var
      maxvar = \case
        Atomic{} -> 0
        Negate g -> maxvar g
        Connected _ g h -> maxvar g `max` maxvar h
        Quantified _ w _ -> w

-- | A smart constructor for universally quantified formulas.
-- Provides a polyvariadic higher-order abstract syntax for the bindings of
-- universally quantified variables.
forall :: Binder b => b -> Formula
forall = quantified Forall

-- | A smart constructor for existentially quantified formulas.
-- Provides a polyvariadic higher-order abstract syntax for the bindings of
-- existentially quantified variables.
exists :: Binder b => b -> Formula
exists = quantified Exists


-- * Monoids of first-order formulas

-- | The ('EmptyClause', '\./') monoid.
newtype ClauseUnion = ClauseUnion { getClauseUnion :: Clause }
  deriving (Show, Eq, Ord)

instance Semigroup ClauseUnion where
  (<>) = coerce (\./)

instance Monoid ClauseUnion where
  mempty = ClauseUnion EmptyClause
  mappend = (<>)

-- | Build the union of a collection of clauses.
clauseUnion :: Foldable f => f Clause -> Clause
clauseUnion = getClauseUnion . mconcat . fmap ClauseUnion . Foldable.toList

-- | The ('Tautology', '/\') monoid.
newtype Conjunction = Conjunction { getConjunction :: Formula }
  deriving (Show, Eq, Ord)

instance Semigroup Conjunction where
  (<>) = coerce (/\)

instance Monoid Conjunction where
  mempty = Conjunction Tautology
  mappend = (<>)

-- | Build the conjunction of formulas in a list.
conjunction :: Foldable f => f Formula -> Formula
conjunction = getConjunction . mconcat . fmap Conjunction . Foldable.toList

-- | The ('Falsum', '\/') monoid.
newtype Disjunction = Disjunction { getDisjunction :: Formula }
  deriving (Show, Eq, Ord)

instance Semigroup Disjunction where
  (<>) = coerce (\/)

instance Monoid Disjunction where
  mempty = Disjunction Falsum
  mappend = (<>)

-- | Build the disjunction of formulas in a list.
disjunction :: Foldable f => f Formula -> Formula
disjunction = getDisjunction . mconcat . fmap Disjunction . Foldable.toList

-- | The ('Tautology', '<=>') monoid.
newtype Equivalence = Equivalence { getEquivalence :: Formula }
  deriving (Show, Eq, Ord)

instance Semigroup Equivalence where
  (<>) = coerce (<=>)

instance Monoid Equivalence where
  mempty = Equivalence Tautology
  mappend = (<>)

-- | Build the equivalence of formulas in a list.
equivalence :: Foldable f => f Formula -> Formula
equivalence = getEquivalence . mconcat . fmap Equivalence . Foldable.toList

-- | The ('Falsum', '<~>') monoid.
newtype Inequivalence = Inequivalence { getInequivalence :: Formula }
  deriving (Show, Eq, Ord)

instance Semigroup Inequivalence where
  (<>) = coerce (<~>)

instance Monoid Inequivalence where
  mempty = Inequivalence Falsum
  mappend = (<>)

-- | Build the inequivalence of formulas in a list.
inequivalence :: Foldable f => f Formula -> Formula
inequivalence = getInequivalence . mconcat . fmap Inequivalence . Foldable.toList
