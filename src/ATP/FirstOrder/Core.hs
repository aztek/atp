{-# LANGUAGE CPP #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE DeriveFunctor, DeriveTraversable, DeriveFoldable #-}

{-|
Module       : ATP.FirstOrder.Core
Description  : Data types representing unsorted first-order logic.
Copyright    : (c) Evgenii Kotelnikov, 2019-2020
License      : GPL-3
Maintainer   : evgeny.kotelnikov@gmail.com
Stability    : experimental
-}

module ATP.FirstOrder.Core (
  -- * First-order logic
  Var,
  Symbol,
  Term(..),
  Literal(..),
  Sign(..),
  Signed(..),
  sign,
  Clause(..),
  Connective(..),
  isAssociative,
  Quantifier(..),
  Formula(..),
  LogicalExpression(..),

  -- * Syntactic sugar
  -- $sugar
  Function,
  Constant,
  UnaryFunction,
  BinaryFunction,
  TernaryFunction,
  pattern UnaryFunction,
  pattern BinaryFunction,
  pattern TernaryFunction,

  Predicate,
  UnaryPredicate,
  BinaryPredicate,
  TernaryPredicate,
  pattern UnaryPredicate,
  pattern BinaryPredicate,
  pattern TernaryPredicate,

  pattern FalsumLiteral,
  pattern TautologyLiteral,

  pattern EmptyClause,
  pattern UnitClause,
  pattern TautologyClause,

  pattern Tautology,
  pattern Falsum
) where

#if !MIN_VERSION_base(4, 11, 0)
import Data.Semigroup (Semigroup(..))
#endif
import Data.String (IsString(..))
import Data.Text (Text)


-- * First-order logic

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

-- | The sign of a logical expression is either positive or negative.
data Sign
  = Positive
  | Negative
  deriving (Eq, Show, Ord, Enum, Bounded)

instance Semigroup Sign where
  Negative <> Positive = Negative
  Positive <> Negative = Negative
  Negative <> Negative = Positive
  Positive <> Positive = Positive

instance Monoid Sign where
  mempty = Positive
  mappend = (<>)

-- | A signed expression is that annotated with a 'Sign'.
data Signed e = Signed {
  signof :: Sign,
  unsign :: e
} deriving (Eq, Show, Ord, Functor, Foldable, Traversable)

-- | Juxtapose a given signed expression with a given sign.
sign :: Sign -> Signed e -> Signed e
sign s (Signed z e) = Signed (s <> z) e

instance Applicative Signed where
  pure = Signed Positive
  Signed s f <*> e = sign s (fmap f e)

instance Monad Signed where
  Signed s e >>= f = sign s (f e)

-- | The first-order clause - an explicitly universally-quantified disjunction
-- of positive or negative literals, represented as a list of signed literals.
newtype Clause = Literals { unClause :: [Signed Literal] }
  deriving (Show, Eq, Ord)

instance Semigroup Clause where
  Literals ls <> Literals ms = Literals (ls <> ms)

instance Monoid Clause where
  mempty = Literals []
  mappend = (<>)

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

-- | Check associativity of a given connective.
--
-- >>> isAssociative Implies
-- False
--
-- >>> isAssociative And
-- True
isAssociative :: Connective -> Bool
isAssociative = \case
  And        -> True
  Or         -> True
  Implies    -> False
  Equivalent -> False
  Xor        -> False

-- | The formula in first-order logic.
data Formula
  = Atomic Literal
  | Negate Formula
  | Connected Connective Formula Formula
  | Quantified Quantifier Var Formula
  deriving (Show, Eq, Ord)

-- | A logical expression is either a clause or a formula.
data LogicalExpression
  = Clause Clause
  | Formula Formula
  deriving (Show, Eq, Ord)


-- * Syntactic sugar

-- $sugar
--
-- Instances, type synonyms and pattern synonyms for syntactic convenience.

instance IsString Term where
  fromString = flip Function [] . fromString

instance IsString Literal where
  fromString = flip Predicate [] . fromString

instance IsString Formula where
  fromString = Atomic . fromString


-- ** Function symbols

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

-- | Build a unary function from a function symbol.
pattern UnaryFunction :: Symbol -> UnaryFunction
pattern UnaryFunction f a = Function f [a]

-- | Build a binary function from a function symbol.
pattern BinaryFunction :: Symbol -> BinaryFunction
pattern BinaryFunction f a b = Function f [a, b]

-- | Build a ternary function from a function symbol.
pattern TernaryFunction :: Symbol -> TernaryFunction
pattern TernaryFunction f a b c = Function f [a, b, c]


-- ** Predicate symbols

-- | The type of a predicate symbol - a mapping from zero or more terms
-- to a formula.
type Predicate = [Term] -> Formula

-- | The type of a predicate symbol with one argument.
type UnaryPredicate = Term -> Formula

-- | The type of a predicate symbol with two arguments.
type BinaryPredicate = Term -> Term -> Formula

-- | The type of a function symbol with three arguments.
type TernaryPredicate = Term -> Term -> Term -> Formula

-- | Build a unary predicate from a predicate symbol.
pattern UnaryPredicate :: Symbol -> UnaryPredicate
pattern UnaryPredicate p a = Atomic (Predicate p [a])

-- | Build a binary predicate from a predicate symbol.
pattern BinaryPredicate :: Symbol -> BinaryPredicate
pattern BinaryPredicate p a b = Atomic (Predicate p [a, b])

-- | Build a ternary predicate from a predicate symbol.
pattern TernaryPredicate :: Symbol -> TernaryPredicate
pattern TernaryPredicate p a b c = Atomic (Predicate p [a, b, c])


-- ** Literals

-- | The positive falsum literal.
pattern FalsumLiteral :: Signed Literal
pattern FalsumLiteral = Signed Positive (Constant False)

-- | The positive tautology literal.
pattern TautologyLiteral :: Signed Literal
pattern TautologyLiteral = Signed Positive (Constant True)


-- ** Clauses

-- | The empty clause.
-- 'EmptyClause' is semantically (but not syntactically) equivalent to 'Falsum'.
pattern EmptyClause :: Clause
pattern EmptyClause = Literals []

-- | The unit clause.
pattern UnitClause :: Signed Literal -> Clause
pattern UnitClause l = Literals [l]

-- | A unit clause with a single positive tautology.
-- 'TautologyClause' is semantically (but not syntactically) equivalent to
-- 'Tautology'.
pattern TautologyClause :: Clause
pattern TautologyClause = UnitClause TautologyLiteral


-- ** Formulas

-- | The logical truth.
pattern Tautology :: Formula
pattern Tautology = Atomic (Constant True)

-- | The logical false.
-- 'Falsum' is semantically (but not syntactically) equivalent to 'EmptyClause'.
pattern Falsum :: Formula
pattern Falsum = Atomic (Constant False)
