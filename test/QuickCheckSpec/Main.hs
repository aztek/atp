{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TemplateHaskell #-}

{-|
Module       : Main
Description  : QuickCheck properties of the atp library.
Copyright    : (c) Evgenii Kotelnikov, 2019
License      : GPL-3
Maintainer   : evgeny.kotelnikov@gmail.com
Stability    : experimental
-}

module Main (main) where

import Control.Monad (unless)
import Data.Function (on)
import qualified Data.Set as S (union)
import System.Exit (exitFailure)

import Test.QuickCheck (
    Property, (===), (==>), whenFail, counterexample,
    forAllProperties, quickCheckWithResult, stdArgs, Args(..)
  )

import ATP.FOL hiding ((===), (==>))
import ATP.Codec.TPTP

import QuickCheckSpec.Generators.FOL ()


-- * Helper functions

-- | Like '(===)', but for alpha equivalence.
(~==) :: (Eq e, Show e, FirstOrder e) => e -> e -> Property
a ~== b = counterexample (show a ++ " ~/= " ++ show b) (a ~= b)


-- * Free and bound variables

freeBoundVars :: (Eq e, Show e, FirstOrder e) => e -> Property
freeBoundVars e = free e `S.union` bound e === vars e

prop_freeBoundVarsFormula :: Formula -> Property
prop_freeBoundVarsFormula = freeBoundVars

prop_freeBoundVarsClause :: Clause -> Property
prop_freeBoundVarsClause = freeBoundVars

prop_freeBoundVarsLiteral :: Literal -> Property
prop_freeBoundVarsLiteral = freeBoundVars

prop_freeBoundVarsTerm :: Term -> Property
prop_freeBoundVarsTerm = freeBoundVars


-- * Alpha conversions

-- ** Alpha equivalence is reflexive

alphaEquivalenceReflexivity :: (Eq e, Show e, FirstOrder e) => e -> Property
alphaEquivalenceReflexivity e =
  whenFail (print $ alpha e e) $
    e ~= e

prop_alphaEquivalenceReflexivityFormula :: Formula -> Property
prop_alphaEquivalenceReflexivityFormula = alphaEquivalenceReflexivity

prop_alphaEquivalenceReflexivityClause :: Clause -> Property
prop_alphaEquivalenceReflexivityClause = alphaEquivalenceReflexivity

prop_alphaEquivalenceReflexivityLiteral :: Literal -> Property
prop_alphaEquivalenceReflexivityLiteral = alphaEquivalenceReflexivity

prop_alphaEquivalenceReflexivityTerm :: Term -> Property
prop_alphaEquivalenceReflexivityTerm = alphaEquivalenceReflexivity

-- ** Alpha equivalence is symmetric

alphaEquivalenceSymmetry :: (Eq e, Show e, FirstOrder e) => e -> e -> Property
alphaEquivalenceSymmetry a b =
  whenFail (print $ alpha a b) $
    whenFail (print $ alpha b a) $
      a ~= b == b ~= a

prop_alphaEquivalenceSymmetryFormula :: Formula -> Formula -> Property
prop_alphaEquivalenceSymmetryFormula = alphaEquivalenceSymmetry

prop_alphaEquivalenceSymmetryClause :: Formula -> Formula -> Property
prop_alphaEquivalenceSymmetryClause = alphaEquivalenceSymmetry

prop_alphaEquivalenceSymmetryLiteral :: Literal -> Literal -> Property
prop_alphaEquivalenceSymmetryLiteral = alphaEquivalenceSymmetry

prop_alphaEquivalenceSymmetryTerm :: Term -> Term -> Property
prop_alphaEquivalenceSymmetryTerm = alphaEquivalenceSymmetry

-- ** Alpha equivalence is transitive

alphaEquivalenceTransitivity :: (Eq e, Show e, FirstOrder e)
                             => e -> e -> e -> Property
alphaEquivalenceTransitivity a b c =
  whenFail (print $ alpha a b) $
    whenFail (print $ alpha b c) $
      whenFail (print $ alpha a c) $
        a ~= b ==>
          b ~= c ==>
            a ~= c

prop_alphaEquivalenceTransitivityFormula :: Formula -> Formula -> Formula -> Property
prop_alphaEquivalenceTransitivityFormula = alphaEquivalenceTransitivity

prop_alphaEquivalenceTransitivityClause :: Clause -> Clause -> Clause -> Property
prop_alphaEquivalenceTransitivityClause = alphaEquivalenceTransitivity

prop_alphaEquivalenceTransitivityLiteral :: Literal -> Literal -> Literal -> Property
prop_alphaEquivalenceTransitivityLiteral = alphaEquivalenceTransitivity

prop_alphaEquivalenceTransitivityTerm :: Term -> Term -> Term -> Property
prop_alphaEquivalenceTransitivityTerm = alphaEquivalenceTransitivity


-- * Simplification

-- ** Clauses

prop_simplifyClauseEliminatesNegatedConstants :: Clause -> Property
prop_simplifyClauseEliminatesNegatedConstants c =
  whenFail (print s) $
    all (not . isNegatedConstant) (unClause s)
      where s = simplifyClause c

isNegatedConstant :: Signed Literal -> Bool
isNegatedConstant = \case
  Signed Negative Constant{} -> True
  _ -> False

prop_simplifyClauseEliminatesFalsum :: Clause -> Property
prop_simplifyClauseEliminatesFalsum c =
  whenFail (print s) $
    FalsumLiteral `notElem` unClause s
      where s = simplifyClause c

prop_simplifyClauseEliminatesRedundantTautology :: Clause -> Property
prop_simplifyClauseEliminatesRedundantTautology c =
  whenFail (print s) $
    s == TautologyClause || TautologyLiteral `notElem` unClause s
      where s = simplifyClause c


-- ** Formulas

prop_simplifyFormulaEliminatesDoubleNegation :: Formula -> Property
prop_simplifyFormulaEliminatesDoubleNegation f =
  whenFail (print g) $
    not (containsDoubleNegation g)
      where g = simplifyFormula f

containsDoubleNegation :: Formula -> Bool
containsDoubleNegation = \case
  Tautology -> False
  Falsum    -> False
  Atomic{}  -> False
  Negate Negate{} -> True
  Negate f -> containsDoubleNegation f
  Connected  _ f g -> containsDoubleNegation f || containsDoubleNegation g
  Quantified _ _ f -> containsDoubleNegation f

prop_simplifyFormulaEliminatesLeftAssocitivity :: Formula -> Property
prop_simplifyFormulaEliminatesLeftAssocitivity f =
  whenFail (print g) $
    not (containsLeftAssocitivity g)
      where g = simplifyFormula f

containsLeftAssocitivity :: Formula -> Bool
containsLeftAssocitivity = \case
  Tautology -> False
  Falsum    -> False
  Atomic{}  -> False
  Negate f  -> containsLeftAssocitivity f
  Connected  c (Connected c' _ _) _ | c' == c && isAssociative c -> True
  Connected  _ f g -> containsLeftAssocitivity f || containsLeftAssocitivity g
  Quantified _ _ f -> containsLeftAssocitivity f


-- ** Idempotence

prop_simplifyIdempotentClause :: Clause -> Property
prop_simplifyIdempotentClause c = simplifyClause c ==~ c
  where
    (==~) = (===) `on` simplifyClause

prop_simplifyIdempotentFormula :: Formula -> Property
prop_simplifyIdempotentFormula f = simplifyFormula f ==~ f
  where
    (==~) = (===) `on` simplifyFormula

prop_simplifyIdempotentLogicalExpression :: LogicalExpression -> Property
prop_simplifyIdempotentLogicalExpression e = simplify e ==~ e
  where
    (==~) = (===) `on` simplify


-- * Conversions

prop_liftUnliftSignedLiteral :: Signed Literal -> Property
prop_liftUnliftSignedLiteral s =
  unliftSignedLiteral (liftSignedLiteral s) === Just s

prop_liftUnliftClause :: Clause -> Property
prop_liftUnliftClause c = unliftClause (liftClause c) ==~ Just c
  where
    (==~) = (===) `on` fmap simplifyClause


-- * Codec

prop_codecClause :: Clause -> Property
prop_codecClause c = c ~==~ decodeClause (encodeClause c)
  where
    (~==~) = (~==) `on` simplifyClause

prop_codecFormula :: Formula -> Property
prop_codecFormula f = f ~==~ decodeFormula (encodeFormula f)
  where
    (~==~) = (~==) `on` simplifyFormula

prop_codec :: LogicalExpression -> Property
prop_codec e = e ~==~ decode (encode e)
  where
    (~==~) = (~==) `on` simplify


-- * Runner

return []

main :: IO ()
main = do
  success <- $forAllProperties $ quickCheckWithResult stdArgs{maxSuccess=1000}
  unless success exitFailure
