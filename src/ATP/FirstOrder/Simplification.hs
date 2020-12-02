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
  simplify,
  simplifyClause,
  simplifyClauses,
  simplifyFormula
) where

import ATP.FirstOrder.Core
import ATP.FirstOrder.Smart

-- $setup
-- >>> :set -XOverloadedStrings
-- >>> :load QuickCheckSpec.Generators


-- * Simplification

-- | Simplify the given formula by replacing each of its constructors with
-- corresponding smart constructors.
simplify :: LogicalExpression -> LogicalExpression
simplify = \case
  Clause  c -> Clause  (simplifyClause  c)
  Formula f -> Formula (simplifyFormula f)

-- | Simplify the given clause by replacing the 'Literals' constructor with
-- the smart constructor 'clause'. The effects of simplification are
-- the following.
--
-- * @'simplifyClause c'@ does not contain negative constant literals.
-- * @'simplifyClause c'@ does not contain falsum literals.
-- * @'simplifyClause c'@ does not contain redundant tautology literals.
--
-- >>> simplifyClause (UnitClause (Signed Negative (Constant True)))
-- Literals {unClause = []}
--
-- >>> simplifyClause (Literals [FalsumLiteral, Signed Positive (Predicate "p" [])])
-- Literals {unClause = [Signed {signof = Positive, unsign = Predicate (PredicateSymbol "p") []}]}
--
-- >>> simplifyClause (Literals [TautologyLiteral, Signed Positive (Predicate "p" [])])
-- Literals {unClause = [Signed {signof = Positive, unsign = Constant True}]}
--
simplifyClause :: Clause -> Clause
simplifyClause = clause . unClause

-- | Simplify the given clause set by replacing the 'Clauses' constructor with
-- the smart constructor 'clauses'. The effects of simplification are
-- the following.
--
-- * @'simplifyClauses c'@ does not contain negative constant literals.
-- * @'simplifyClauses c'@ does not contain falsum literals.
-- * @'simplifyClauses c'@ does not contain tautology literals.
-- * @'simplifyClauses c'@ does not contain redundant falsum literals.
--
-- >>> simplifyClauses (SingleClause (UnitClause (Signed Negative (Constant True))))
-- Clauses {unClauses = [Literals {unClause = []}]}
--
-- >>> simplifyClauses (SingleClause (Literals [FalsumLiteral, Signed Positive (Predicate "p" [])]))
-- Clauses {unClauses = [Literals {unClause = [Signed {signof = Positive, unsign = Predicate (PredicateSymbol "p") []}]}]}
--
-- >>> simplifyClauses (SingleClause (Literals [TautologyLiteral, Signed Positive (Predicate "p" [])]))
-- Clauses {unClauses = []}
--
simplifyClauses :: Clauses -> Clauses
simplifyClauses = clauses . unClauses

-- | Simplify the given formula by replacing each of its constructors with
-- corresponding smart constructors. The effects of simplification are
-- the following.
--
-- * @'simplifyFormula' f@ does not contain nested negations.
-- * All chained applications of any binary connective inside
--   @'simplifyFormula' f@ are right-associative.
--
-- Any formula built only using smart constructors is simplified by construction.
--
-- >>> simplifyFormula (Connected Or tautology (Atomic (Predicate "p" [])))
-- Atomic (Constant True)
--
-- >>> simplifyFormula (Negate (Negate (Atomic (Predicate "p" []))))
-- Atomic (Predicate "p" [])
--
-- >>> simplifyFormula (Connected And (Connected And (Atomic (Predicate "p" [])) (Atomic (Predicate "q" []))) (Atomic (Predicate "r" [])))
-- Connected And (Atomic (Predicate "p" [])) (Connected And (Atomic (Predicate "q" [])) (Atomic (Predicate "r" [])))
--
simplifyFormula :: Formula -> Formula
simplifyFormula = \case
  Atomic l         -> Atomic l
  Negate f         -> neg (simplifyFormula f)
  Connected  c f g -> simplifyFormula f # simplifyFormula g where (#) = smartConnective c
  Quantified q v f -> quantified q (v, simplifyFormula f)

-- | Convert a binary connective to its corresponding smart constructor.
smartConnective :: Connective -> Formula -> Formula -> Formula
smartConnective = \case
  And        -> (/\)
  Or         -> (\/)
  Implies    -> (==>)
  Equivalent -> (<=>)
  Xor        -> (<~>)
