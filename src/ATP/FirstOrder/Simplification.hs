{-# LANGUAGE CPP #-}
{-# LANGUAGE LambdaCase #-}

{-|
Module       : ATP.FirstOrder.Simplification
Description  : Simplification of first-order expressions.
Copyright    : (c) Evgenii Kotelnikov, 2019-2020
License      : GPL-3
Maintainer   : evgeny.kotelnikov@gmail.com
Stability    : experimental
-}
module ATP.FirstOrder.Simplification (
  -- * Simplification
  Simplify(..)
) where

import ATP.FirstOrder.Core
import ATP.FirstOrder.Smart

-- $setup
-- >>> :set -XOverloadedStrings
-- >>> :load Property.Generators


-- * Simplification

-- | A class of first-order expressions that 'simplify' syntactically shrinks
-- while preserving their evaluation.
class Simplify a where
  simplify :: a -> a

-- | Simplify the given formula by replacing each of its constructors with
-- corresponding smart constructors.
instance Simplify LogicalExpression where
  simplify = \case
    Clause  c -> Clause  (simplify c)
    Formula f -> Formula (simplify f)

-- | Simplify the given clause by replacing the 'Literals' constructor with
-- the smart constructor 'clause'. The effects of simplification are
-- the following.
--
-- * @'simplify' c@ does not contain negative constant literals.
-- * @'simplify' c@ does not contain falsum literals.
-- * @'simplify' c@ does not contain redundant tautology literals.
--
-- >>> simplify (UnitClause (Signed Negative (Constant True)))
-- Literals {getLiterals = []}
--
-- >>> simplify (Literals [FalsumLiteral, Signed Positive (Predicate "p" [])])
-- Literals {getLiterals = [Signed {signof = Positive, unsign = Predicate (PredicateSymbol "p") []}]}
--
-- >>> simplify (Literals [TautologyLiteral, Signed Positive (Predicate "p" [])])
-- Literals {getLiterals = [Signed {signof = Positive, unsign = Constant True}]}
--
instance Simplify Clause where
  simplify = clause . getLiterals

-- | Simplify the given clause set by replacing the 'Clauses' constructor with
-- the smart constructor 'clauses'. The effects of simplification are
-- the following.
--
-- * @'simplify' c@ does not contain negative constant literals.
-- * @'simplify' c@ does not contain falsum literals.
-- * @'simplify' c@ does not contain tautology literals.
-- * @'simplify' c@ does not contain redundant falsum literals.
--
-- >>> simplify (SingleClause (UnitClause (Signed Negative (Constant True))))
-- Clauses {getClauses = [Literals {getLiterals = []}]}
--
-- >>> simplify (SingleClause (Literals [FalsumLiteral, Signed Positive (Predicate "p" [])]))
-- Clauses {getClauses = [Literals {getLiterals = [Signed {signof = Positive, unsign = Predicate (PredicateSymbol "p") []}]}]}
--
-- >>> simplify (SingleClause (Literals [TautologyLiteral, Signed Positive (Predicate "p" [])]))
-- Clauses {getClauses = []}
--
instance Simplify Clauses where
  simplify = clauses . getClauses

-- | Simplify the given formula by replacing each of its constructors with
-- corresponding smart constructors. The effects of simplification are
-- the following.
--
-- * @'simplify' f@ does not contain nested negations.
-- * All chained applications of any binary connective inside
--   @'simplify' f@ are right-associative.
--
-- Any formula built only using smart constructors is simplified by construction.
--
-- >>> simplify (Connected Or tautology (Atomic (Predicate "p" [])))
-- Atomic (Constant True)
--
-- >>> simplify (Negate (Negate (Atomic (Predicate "p" []))))
-- Atomic (Predicate "p" [])
--
-- >>> simplify (Connected And (Connected And (Atomic (Predicate "p" [])) (Atomic (Predicate "q" []))) (Atomic (Predicate "r" [])))
-- Connected And (Atomic (Predicate "p" [])) (Connected And (Atomic (Predicate "q" [])) (Atomic (Predicate "r" [])))
--
instance Simplify Formula where
  simplify = \case
    Atomic l -> Atomic l
    Negate f -> neg (simplify f)
    Connected  c f g -> simplify f # simplify g where (#) = smartConnective c
    Quantified q v f -> quantified q (v, simplify f)

-- | Convert a binary connective to its corresponding smart constructor.
smartConnective :: Connective -> Formula -> Formula -> Formula
smartConnective = \case
  And        -> (/\)
  Or         -> (\/)
  Implies    -> (==>)
  Equivalent -> (<=>)
  Xor        -> (<~>)

-- | Simplify the given theorem by flattening the conjunction of its premises
-- and its conjecture.
instance Simplify Theorem where
  simplify (Theorem as c) = flattenConjunction (fmap simplify as) |- simplify c
