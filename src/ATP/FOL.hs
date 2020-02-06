{-# LANGUAGE CPP #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveFunctor, DeriveTraversable, DeriveFoldable #-}

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
  Sign(..),
  Signed(..),
  sign,
  Clause(..),
  Connective(..),
  isAssociative,
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

  -- * Simplification
  simplify,

  -- * Variables
  Substitution,
  effective,
  eliminatesVariable,
  eliminatesVariables,
  independent,
  FirstOrder(..),
  closed,
  close,
  unprefix,

  -- * Monoids of first-order formulas
  Conjunction(..),
  conjunction,
  Disjunction(..),
  disjunction,
  Equivalence(..),
  equivalence,
  Inequivalence(..),
  inequivalence,

  -- * Conversions
  liftSignedLiteral,
  unliftSignedLiteral,
  liftClause,
  unliftClause,

  -- * Theorems
  Theorem(..),
  (|-),
  claim
) where

import Control.Monad (foldM, zipWithM, liftM2, guard)
import qualified Data.Foldable as Foldable (toList)
#if !MIN_VERSION_base(4, 8, 0)
import Data.Foldable (Foldable)
import Data.Monoid (Monoid(..))
#endif
import Data.Function (on)
import Data.Functor (($>))
import qualified Data.Map as M
import Data.Map (Map)
import Data.Maybe (isJust)
#if !MIN_VERSION_base(4, 11, 0)
import Data.Semigroup (Semigroup(..))
#endif
import qualified Data.Set as S
import Data.Set (Set)
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


-- * Simplification

-- | Simplifies the given formula by replacing each of its constructors with
-- corresponding smart constructors. The effects of simplification are the following.
--
-- * @'simplify' f@ does not contain nested negations.
-- * All chained applications of any binary connective inside @'simplify' f@ are
--   right-associative.
--
-- Any formula built only using smart constructors is simplified by construction.
--
-- >>> simplify (Connected tautology Or (Atomic (Predicate "p" [])))
-- Atomic (Constant True)
--
-- >>> simplify (Negate (Negate (Atomic (Predicate "p" []))))
-- Atomic (Predicate "p" [])
--
-- >>> simplify (Connected (Connected (Atomic (Predicate "p" [])) And (Atomic (Predicate "q" []))) And (Atomic (Predicate "r" [])))
-- Connected (Atomic (Predicate "p" [])) And (Connected (Atomic (Predicate "q" [])) And (Atomic (Predicate "r" [])))
--
simplify :: Formula -> Formula
simplify = \case
  Atomic l         -> Atomic l
  Negate f         -> neg (simplify f)
  Connected f c g  -> simplify f # simplify g where (#) = smartConnective c
  Quantified q v f -> quantified q (v, simplify f)

-- | Convert a binary connective to its corresponding smart constructor.
smartConnective :: Connective -> Formula -> Formula -> Formula
smartConnective = \case
  And        -> (/\)
  Or         -> (\/)
  Implies    -> (==>)
  Equivalent -> (<=>)
  Xor        -> (<~>)


-- * Conversions

-- | Convert a clause to a full first-order formula.
liftClause :: Clause -> Formula
liftClause = close . disjunction . fmap liftSignedLiteral . unClause

-- | Try to convert a first-order formula /f/ to a clause.
-- This function succeeds if /f/ is a tree of disjunctions of
-- (negated) atomic formula.
unliftClause :: Formula -> Maybe Clause
unliftClause = unlift . unprefix
  where
    unlift = \case
      Connected f Or g -> mappend <$> unlift f <*> unlift g
      f -> fmap (\l -> Literals [l]) (unliftSignedLiteral f)

-- | Convert a signed literal to a (negated) atomic formula.
liftSignedLiteral :: Signed Literal -> Formula
liftSignedLiteral (Signed s l) = case s of
  Positive -> Atomic l
  Negative -> Negate (Atomic l)

-- | Try to convert a first-order formula /f/ to a signed literal.
-- This function succeeds if /f/ is a (negated) atomic formula.
unliftSignedLiteral :: Formula -> Maybe (Signed Literal)
unliftSignedLiteral = \case
  Atomic l -> Just (Signed Positive l)
  Negate f -> sign Negative <$> unliftSignedLiteral f
  _ -> Nothing


-- * Variables

-- | The parallel substitution of a set of variables.
type Substitution = Map Var Term

-- | @'eliminatesVariable' v s@ is true iff 's' substituted the variable 'v'
-- with a term where 'v' does not occur.
--
-- > eliminatesVariable v s ==> not (v `freeIn` substitute s e)
--
eliminatesVariable :: Var -> Substitution -> Bool
eliminatesVariable v s = M.member v s && not (any (freeIn v) (M.elems s))

-- | @'effective' s e@ checks whether 's' substitutes any of the variables
-- that occur freely in 'e'.
--
-- > not (effective s e) ==> substitute s e === e
--
effective :: FirstOrder e => Substitution -> e -> Bool
effective s e = any (`freeIn` e) (M.keys s)

-- | @'eliminatesVariables' s@ is true iff 's' substitutes each of its variables
-- /v/ with a term where /v/ does not occur.
--
-- > eliminatesVariables s ==> not $ effective s (substitute s e)
--
eliminatesVariables :: Substitution -> Bool
eliminatesVariables s = all (not . effective s) (M.elems s)

-- | Checks whether two substitutions are independent.
--
-- > independent s s' ==> substitute s (substitute s' e) === substitute s' (substitute s e)
--
independent :: Substitution -> Substitution -> Bool
independent s1 s2 =
  S.disjoint (M.keysSet s1) (M.keysSet s2) &&
  all (`eliminatesVariable` s2) (M.keys s1) &&
  all (`eliminatesVariable` s1) (M.keys s2)

-- | Renaming is an injective mapping of variables.
type Renaming = Map Var Var

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

  -- | Apply the given substitution to the given expression.
  substitute :: Substitution -> e -> e

  -- | Apply the given renaming to the given expression, i.e. subsitute in
  -- parallel all variables in it.
  rename :: Renaming -> e -> e

  -- | @'alpha' a b@ returns 'Nothing' if 'a' cannot be alpha converted to 'b'
  -- and 'Just r', where 'r' is a renaming, otherwise.
  --
  -- > isJust (alpha a b) ==> rename (fromJust $ alpha a b) a === b
  --
  alpha :: e -> e -> Maybe Renaming

  -- | Check whether two given expressions are alpha-equivalent, that is
  -- equivalent up to renaming of variables.
  --
  -- 'alphaEquivalent' is an equivalence relation.
  --
  -- __Symmetry__
  --
  -- > e `alphaEquivalent` e
  --
  -- __Reflexivity__
  --
  -- > a `alphaEquivalent` b == b `alphaEquivalent` a
  --
  -- __Transitivity__
  --
  -- > a `alphaEquivalent` b && b `alphaEquivalent` c ==> a `alphaEquivalent` c
  --
  alphaEquivalent :: e -> e -> Bool
  alphaEquivalent a b = isJust (alpha a b)

insertRenaming :: Renaming -> (Var, Var) -> Maybe Renaming
insertRenaming r (v, v') = guard p $> M.insert v v' r
  where p = maybe (v' `notElem` M.elems r) (== v') (M.lookup v r)

mergeRenamings :: Renaming -> Renaming -> Maybe Renaming
mergeRenamings r = foldM insertRenaming r . M.toList

instance FirstOrder Formula where
  vars = \case
    Atomic l         -> vars l
    Negate f         -> vars f
    Connected f _ g  -> vars f `S.union` vars g
    Quantified _ _ f -> vars f

  free = \case
    Atomic l         -> vars l
    Negate f         -> free f
    Connected f _ g  -> free f `S.union` free g
    Quantified _ v f -> S.delete v (free f)

  bound = \case
    Atomic{}         -> S.empty
    Negate f         -> bound f
    Connected f _ g  -> bound f `S.union` bound g
    Quantified _ v f -> if v `freeIn` f then S.insert v (bound f) else bound f

  substitute s = \case
    Atomic l         -> Atomic (substitute s l)
    Negate f         -> Negate (substitute s f)
    Connected f c g  -> Connected (substitute s f) c (substitute s g)
    Quantified q v f -> Quantified q v (substitute (M.delete v s) f)

  rename r = \case
    Atomic l         -> Atomic (rename r l)
    Negate f         -> Negate (rename r f)
    Connected f c g  -> Connected (rename r f) c (rename r g)
    Quantified q v f -> Quantified q (M.findWithDefault v v r) (rename r f)

  alpha (Atomic l) (Atomic l') = alpha l l'
  alpha (Negate f) (Negate f') = alpha f f'
  alpha (Connected f c g) (Connected f' c' g') | c == c' =
    uncurry mergeRenamings =<< liftM2 (,) (alpha f f') (alpha g g')
  alpha (Quantified q v f) (Quantified q' v' f') | q == q' =
    uncurry mergeRenamings =<< liftM2 (,) (alpha f f') (Just $ M.singleton v v')
  alpha _ _ = Nothing

instance FirstOrder Clause where
  vars  = S.unions . fmap vars . unClause
  free  = S.unions . fmap vars . unClause
  bound = S.unions . fmap vars . unClause

  substitute s = Literals . fmap (substitute s) . unClause
  rename     r = Literals . fmap (rename     r) . unClause

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

  substitute = fmap . substitute
  rename     = fmap . rename

  alpha = alpha `on` unsign
  alphaEquivalent = alphaEquivalent `on` unsign

instance FirstOrder Literal where
  vars = \case
    Constant{}     -> S.empty
    Predicate _ ts -> S.unions (fmap vars ts)
    Equality a b   -> vars a `S.union` vars b

  free = vars

  bound _ = S.empty

  substitute s = \case
    Constant b     -> Constant b
    Predicate p ts -> Predicate p (fmap (substitute s) ts)
    Equality a b   -> Equality (substitute s a) (substitute s b)

  rename = substitute . fmap Variable

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

  substitute s = \case
    Variable v    -> M.findWithDefault (Variable v) v s
    Function f ts -> Function f (fmap (substitute s) ts)

  rename = substitute . fmap Variable

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

-- | Build a logical claim - a conjecture entailed by the empty set of premises.
claim :: Formula -> Theorem
claim f = [] |- f
