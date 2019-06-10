{-# LANGUAGE CPP #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternSynonyms #-}

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

It can be formalized in first-order logic and expressed in Haskell as follows.

> humansAreMortal :: Formula
> humansAreMortal = forall $ \x -> "human" # [x] ==> "mortal" # [x]
>
> socratesIsHuman :: Formula
> socratesIsHuman = "human" # ["socrates"]
>
> socratesIsMortal :: Formula
> socratesIsMortal = "mortal" # ["socrates"]
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
  Application(..),
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
  quantified,
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
-- >>> :load QuickCheckSpec.Generators


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

infix  9 #
infix  8 ===
infix  8 =/=
infixl 7 /\ --
infixl 6 \/
infix  5 ==>
infixl 5 <=>
infixl 5 <~>

-- | A helper type class with the single operator ('#') that represents the
-- application of a function or predicate symbol to a list of terms.
--
-- 'Application' allows ('#') to be used for both terms, literals and formulas
-- and avoids introducing three separate helper functions.
class Application a where
  (#) :: Symbol -> [Term] -> a

instance Application Term where
  (#) = Function

instance Application Literal where
  (#) = Predicate

instance Application Formula where
  p # ts = Atomic (p # ts)

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

-- | A smart constructor for quantified formulas.
quantified :: Quantifier -> Var -> Formula -> Formula
quantified _ _ Tautology = tautology
quantified _ _ Falsum    = falsum
quantified q v f = Quantified q v f

-- | A smart constructor for quantified formulas.
-- Provides a higher-order abstract syntax for the binding of
-- a quantified variable.
--
-- See <https://emilaxelsson.github.io/documents/axelsson2013using.pdf>
-- for details.
quantifiedHOAS :: Quantifier -> (Term -> Formula) -> Formula
quantifiedHOAS q p = quantified q v f
  where
    f = p (Variable v)
    v = 1 + maximalVariable f

    maximalVariable :: Formula -> Var
    maximalVariable = \case
      Atomic{} -> 0
      Negate g -> maximalVariable g
      Connected g _ h -> maximalVariable g `max` maximalVariable h
      Quantified _ w _ -> w

-- | A smart constructor for universally quantified formulas.
-- Provides a higher-order abstract syntax for the binding of
-- a universally quantified variable.
forall :: (Term -> Formula) -> Formula
forall = quantifiedHOAS Forall

-- | A smart constructor for existentially quantified formulas.
-- Provides a higher-order abstract syntax for the binding of
-- an existentially quantified variable.
exists :: (Term -> Formula) -> Formula
exists = quantifiedHOAS Exists


-- * Monoids of first-order formulas

-- | Monoid under ('/\').
newtype Conjunction = Conjunction { getConjunction :: Formula }
  deriving (Show, Eq, Ord)

instance Semigroup Conjunction where
  Conjunction f <> Conjunction g = Conjunction (f /\ g)

instance Monoid Conjunction where
  mempty = Conjunction tautology
  mappend = (<>)

-- | Build the conjunction of formulas in a list.
conjunction :: [Formula] -> Formula
conjunction = getConjunction . mconcat . fmap Conjunction

-- | Monoid under ('\/').
newtype Disjunction = Disjunction { getDisjunction :: Formula }
  deriving (Show, Eq, Ord)

instance Semigroup Disjunction where
  Disjunction f <> Disjunction g = Disjunction (f \/ g)

instance Monoid Disjunction where
  mempty = Disjunction falsum
  mappend = (<>)

-- | Build the disjunction of formulas in a list.
disjunction :: [Formula] -> Formula
disjunction = getDisjunction . mconcat . fmap Disjunction

-- | Monoid under ('<=>').
newtype Equivalence = Equivalence { getEquivalence :: Formula }
  deriving (Show, Eq, Ord)

instance Semigroup Equivalence where
  Equivalence f <> Equivalence g = Equivalence (f <=> g)

instance Monoid Equivalence where
  mempty = Equivalence tautology
  mappend = (<>)

-- | Build the equivalence of formulas in a list.
equivalence :: [Formula] -> Formula
equivalence = getEquivalence . mconcat . fmap Equivalence

-- | Monoid under ('<~>').
newtype Inequivalence = Inequivalence { getInequivalence :: Formula }
  deriving (Show, Eq, Ord)

instance Semigroup Inequivalence where
  Inequivalence f <> Inequivalence g = Inequivalence (f <~> g)

instance Monoid Inequivalence where
  mempty = Inequivalence falsum
  mappend = (<>)

-- | Build the inequivalence of formulas in a list.
inequivalence :: [Formula] -> Formula
inequivalence = getInequivalence . mconcat . fmap Inequivalence


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
