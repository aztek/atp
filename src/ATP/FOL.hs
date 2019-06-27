{-# LANGUAGE CPP #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE FlexibleInstances #-}

{-|
Module       : ATP.FOL
Description  : Formulas in unsorted first-order logic.
Copyright    : (c) Evgenii Kotelnikov, 2019
License      : GPL-3
Maintainer   : evgeny.kotelnikov@gmail.com
Stability    : experimental

Data structures that represent formulas and theorems in first-order logic,
and smart constructors for them.

Consider the following classical logical syllogism.

/All humans are mortal. Socrates is a human. Therefore, Socrates is mortal./

We can formalize it in first-order logic and express in Haskell as follows.

> human, mortal :: UnaryPredicate
> human = unaryPredicate "human"
> mortal = unaryPredicate "mortal"
>
> socrates :: Constant
> socrates = "socrates"
>
> humansAreMortal :: Formula
> humansAreMortal = forall $ \x -> human x ==> mortal x
>
> socratesIsHuman :: Formula
> socratesIsHuman = human socrates
>
> socratesIsMortal :: Formula
> socratesIsMortal = mortal socrates
>
> syllogism :: Theorem
> syllogism = [humansAreMortal, socratesIsHuman] |- socratesIsMortal
-}

module ATP.FOL (
  -- * Formulas
  Var,
  Symbol,
  Term(..),
  Literal(..),
  Connective(..),
  Quantifier(..),
  Formula(..),

  -- * Smart constructors
  Function,
  Constant,
  UnaryFunction,
  BinaryFunction,
  TernaryFunction,
  function,
  unaryFunction,
  binaryFunction,
  ternaryFunction,
  Predicate,
  UnaryPredicate,
  BinaryPredicate,
  TernaryPredicate,
  predicate,
  unaryPredicate,
  binaryPredicate,
  ternaryPredicate,
  tautology,
  pattern Tautology,
  falsum,
  pattern Falsum,
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

  -- * Monoids of first-order formulas
  Conjunction(..),
  conjunction,
  Disjunction(..),
  disjunction,
  Equivalence(..),
  equivalence,
  Inequivalence(..),
  inequivalence,

  -- * Theorems
  Theorem(..),
  (|-)
) where

import qualified Data.Foldable as Foldable (toList)
#if !MIN_VERSION_base(4, 8, 0)
import Data.Foldable (Foldable)
import Data.Monoid (Monoid(..))
#endif
#if !MIN_VERSION_base(4, 11, 0)
import Data.Semigroup (Semigroup(..))
#endif
import Data.String (IsString(..))
import Data.Text (Text)

-- $setup
-- >>> :set -XOverloadedStrings
-- >>> :load QuickCheckSpec.Generators
-- >>> let eq = binaryPredicate "eq"


-- * Formulas

-- | The type of variables in first-order formulas.
type Var = Integer

-- | The type of function and predicate symbols in first-order formulas.
type Symbol = Text

-- | The term in first-order logic.
data Term
  = Variable Var
    -- ^ A quantified variable.
  | Function Symbol [Term]
    -- ^ Application of a function symbol. The empty list of arguments
    -- represents a constant.
  deriving (Show, Eq, Ord)

instance IsString Term where
  fromString = flip Function [] . fromString

-- | The literal in first-order logic.
data Literal
  = Constant Bool
    -- ^ A logical constant - tautology or falsum.
  | Predicate Symbol [Term]
    -- ^ Application of a predicate symbol. The empty list of arguments
    -- represents a boolean constant.
  | Equality Term Term
    -- ^ Equality between terms.
  deriving (Show, Eq, Ord)

instance IsString Literal where
  fromString = flip Predicate [] . fromString

-- | The quantifier in first-order logic.
data Quantifier
  = Forall -- ^ The universal quantifier.
  | Exists -- ^ The existential quantifier.
  deriving (Eq, Show, Ord, Enum, Bounded)

-- | The binary connective in first-order logic.
data Connective
  = And        -- ^ Conjunction.
  | Or         -- ^ Disjunction.
  | Implies    -- ^ Implication.
  | Equivalent -- ^ Equivalence.
  | Xor        -- ^ Exclusive or.
  deriving (Show, Eq, Ord, Enum, Bounded)

-- | The formula in first-order logic.
data Formula
  = Atomic Literal
  | Negate Formula
  | Connected Formula Connective Formula
  | Quantified Quantifier Var Formula
  deriving (Show, Eq, Ord)

instance IsString Formula where
  fromString = Atomic . fromString


-- * Smart constructors

infix  8 ===
infix  8 =/=
infixl 7 /\ --
infixl 6 \/
infix  5 ==>
infixl 5 <=>
infixl 5 <~>

-- | The type of a function symbol - a mapping from zero or more terms
-- to a term.
type Function = [Term] -> Term

-- | The type of a constant symbol.
type Constant = Term

-- | The type of a function symbol with one argument.
type UnaryFunction = Term -> Term

-- | The type of a function symbol with two arguments.
type BinaryFunction = Term -> Term -> Term

-- | The type of a function symbol with three arguments.
type TernaryFunction = Term -> Term -> Term -> Term

-- | Build a function from a function symbol.
function :: Symbol -> Function
function = Function

-- | Build a unary function from a function symbol.
unaryFunction :: Symbol -> UnaryFunction
unaryFunction f a = Function f [a]

-- | Build a binary function from a function symbol.
binaryFunction :: Symbol -> BinaryFunction
binaryFunction f a b = Function f [a, b]

-- | Build a ternary function from a function symbol.
ternaryFunction :: Symbol -> TernaryFunction
ternaryFunction f a b c = Function f [a, b, c]

-- | The type of a predicate symbol - a mapping from zero or more terms
-- to a formula.
type Predicate = [Term] -> Formula

-- | The type of a predicate symbol with one argument.
type UnaryPredicate = Term -> Formula

-- | The type of a predicate symbol with two arguments.
type BinaryPredicate = Term -> Term -> Formula

-- | The type of a function symbol with three arguments.
type TernaryPredicate = Term -> Term -> Term -> Formula

-- | Build a predicate from a predicate symbol.
predicate :: Symbol -> Predicate
predicate p as = Atomic (Predicate p as)

-- | Build a unary predicate from a predicate symbol.
unaryPredicate :: Symbol -> UnaryPredicate
unaryPredicate p a = Atomic (Predicate p [a])

-- | Build a binary predicate from a predicate symbol.
binaryPredicate :: Symbol -> BinaryPredicate
binaryPredicate p a b = Atomic (Predicate p [a, b])

-- | Build a ternary predicate from a predicate symbol.
ternaryPredicate :: Symbol -> TernaryPredicate
ternaryPredicate p a b c = Atomic (Predicate p [a, b, c])

-- | The logical truth.
tautology :: Formula
tautology = Atomic (Constant True)

-- | The logical truth.
#if __GLASGOW_HASKELL__ >= 710
pattern Tautology :: Formula
#endif
pattern Tautology = Atomic (Constant True)

-- | The logical false.
falsum :: Formula
falsum = Atomic (Constant False)

-- | The logical false.
#if __GLASGOW_HASKELL__ >= 710
pattern Falsum :: Formula
#endif
pattern Falsum = Atomic (Constant False)

-- | A smart constructor for equality.
(===) :: Term -> Term -> Formula
a === b = Atomic (Equality a b)

-- | A smart constructor for inequality.
(=/=) :: Term -> Term -> Formula
a =/= b = Negate (a === b)

-- | A smart constructor for negation.
neg :: Formula -> Formula
neg = \case
  Tautology -> falsum
  Falsum    -> tautology
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
-- prop> tautology /\ g == g
--
-- __Right identity__
--
-- prop> f /\ tautology == f
--
(/\) :: Formula -> Formula -> Formula
Falsum    /\ _ = falsum
Tautology /\ g = g
_ /\ Falsum    = falsum
f /\ Tautology = f
Connected f And g /\ h = f /\ (g /\ h)
f /\ g = Connected f And g

-- | A smart constructor for the 'Or' connective.
-- ('\/') has the following properties.
--
-- __Associativity__
--
-- prop> (f \/ g) \/ h == f \/ (g \/ h)
--
-- __Left identity__
--
-- prop> falsum \/ g == g
--
-- __Right identity__
--
-- prop> f \/ falsum == f
--
(\/) :: Formula -> Formula -> Formula
Tautology \/ _ = tautology
Falsum    \/ g = g
_ \/ Tautology = tautology
f \/ Falsum    = f
Connected f Or g \/ h = f \/ (g \/ h)
f \/ g = Connected f Or g

-- | A smart constructor for the 'Implies' connective.
(==>) :: Formula -> Formula -> Formula
Tautology ==> g = g
Falsum    ==> _ = tautology
_ ==> Tautology = tautology
f ==> Falsum    = neg f
f ==> g = Connected f Implies g

-- | A smart constructor for the 'Equivalent' connective.
-- ('<=>') has the following properties.
--
-- __Associativity__
--
-- prop> (f <=> g) <=> h == f <=> (g <=> h)
--
-- __Left identity__
--
-- prop> tautology <=> g == g
--
-- __Right identity__
--
-- prop> f <=> tautology == f
--
(<=>) :: Formula -> Formula -> Formula
Tautology <=> g = g
f <=> Tautology = f
Connected f Equivalent g <=> h = f <=> (g <=> h)
f <=> g = Connected f Equivalent g

-- | A smart constructor for the 'Xor' connective.
-- ('<~>') has the following properties.
--
-- __Associativity__
--
-- prop> (f <~> g) <~> h == f <~> (g <~> h)
--
-- __Left identity__
--
-- prop> falsum <~> g == g
--
-- __Right identity__
--
-- prop> f <~> falsum == f
--
(<~>) :: Formula -> Formula -> Formula
Falsum <~> g = g
f <~> Falsum = f
Connected f Xor g <~> h = f <~> (g <~> h)
f <~> g = Connected f Xor g

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
-- Quantified Forall 2 (Quantified Forall 1 (Connected (Atomic (Predicate "eq" [Variable 2,Variable 1])) Implies (Atomic (Predicate "eq" [Variable 1,Variable 2]))))
class Binder b where
  -- | A smart constructor for quantified formulas.
  quantified :: Quantifier -> b -> Formula

-- | The degenerate instance - no variable is bound.
instance Binder Formula where
  quantified _ f = f

-- | The recursive instance for polyvariadic bindings of quantified variables.
-- This is a generalized version of
-- <https://emilaxelsson.github.io/documents/axelsson2013using.pdf>.
instance Binder b => Binder (Term -> b) where
  quantified q b = Quantified q v f
    where
      f = quantified q (b (Variable v))
      v = 1 + maxvar f

      maxvar :: Formula -> Var
      maxvar = \case
        Atomic{} -> 0
        Negate g -> maxvar g
        Connected g _ h -> maxvar g `max` maxvar h
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

-- | The ('tautology', '/\') monoid.
newtype Conjunction = Conjunction { getConjunction :: Formula }
  deriving (Show, Eq, Ord)

instance Semigroup Conjunction where
  Conjunction f <> Conjunction g = Conjunction (f /\ g)

instance Monoid Conjunction where
  mempty = Conjunction tautology
  mappend = (<>)

-- | Build the conjunction of formulas in a list.
conjunction :: Foldable f => f Formula -> Formula
conjunction = getConjunction . mconcat . fmap Conjunction . Foldable.toList

-- | The ('falsum', '\/') monoid.
newtype Disjunction = Disjunction { getDisjunction :: Formula }
  deriving (Show, Eq, Ord)

instance Semigroup Disjunction where
  Disjunction f <> Disjunction g = Disjunction (f \/ g)

instance Monoid Disjunction where
  mempty = Disjunction falsum
  mappend = (<>)

-- | Build the disjunction of formulas in a list.
disjunction :: Foldable f => f Formula -> Formula
disjunction = getDisjunction . mconcat . fmap Disjunction . Foldable.toList

-- | The ('tautology', '<=>') monoid.
newtype Equivalence = Equivalence { getEquivalence :: Formula }
  deriving (Show, Eq, Ord)

instance Semigroup Equivalence where
  Equivalence f <> Equivalence g = Equivalence (f <=> g)

instance Monoid Equivalence where
  mempty = Equivalence tautology
  mappend = (<>)

-- | Build the equivalence of formulas in a list.
equivalence :: Foldable f => f Formula -> Formula
equivalence = getEquivalence . mconcat . fmap Equivalence . Foldable.toList

-- | The ('falsum', '<~>') monoid.
newtype Inequivalence = Inequivalence { getInequivalence :: Formula }
  deriving (Show, Eq, Ord)

instance Semigroup Inequivalence where
  Inequivalence f <> Inequivalence g = Inequivalence (f <~> g)

instance Monoid Inequivalence where
  mempty = Inequivalence falsum
  mappend = (<>)

-- | Build the inequivalence of formulas in a list.
inequivalence :: Foldable f => f Formula -> Formula
inequivalence = getInequivalence . mconcat . fmap Inequivalence . Foldable.toList


-- * Theorems

-- | A theorem is zero or more axioms and a conjecture.
data Theorem = Theorem {
  axioms :: [Formula],
  conjecture :: Formula
} deriving (Show, Eq, Ord)

infix 2 |-

-- | Syntactic sugar, a synonym for 'Theorem'.
(|-) :: Foldable f => f Formula -> Formula -> Theorem
as |- c = Theorem (Foldable.toList as) c
