{-# LANGUAGE CPP #-}
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
#if !MIN_VERSION_base(4, 11, 0)
import Data.Semigroup (Semigroup(..))
#endif
import System.Exit (exitFailure)

import Test.QuickCheck (
    Property, property, (===), (==>), whenFail, counterexample, forAll,
    forAllProperties, quickCheckWithResult, stdArgs, Args(..), withMaxSuccess
  )

import ATP hiding ((===), (==>))
import ATP.Error
import ATP.Codec.TPTP

import QuickCheckSpec.Generators.FOL ()
import QuickCheckSpec.Generators.AlphaEquivalent


-- * Helper functions

-- | Like '(===)', but for alpha equivalence.
(~==) :: (Show e, FirstOrder e) => e -> e -> Property
a ~== b = counterexample (show a ++ " ~/= " ++ show b) (a ~= b)

-- | Like '(~==)', but for results of partial computations.
(~~=) :: (Show e, FirstOrder e) => Partial e -> Partial e -> Property
x ~~= y
  | Right a <- liftPartial x, Right b <- liftPartial y = a ~== b
  | otherwise = counterexample (show x ++ " ~/= " ++ show y) False


-- * Generators

-- ** 'genAlphaEquivalent' does not introduce new free variables

freeCountAlphaEquivalent :: (Show e, FirstOrder e) => e -> Property
freeCountAlphaEquivalent a =
  forAll (genAlphaEquivalent a) $ \b ->
    length (free a) === length (free b)

prop_freeCountAlphaEquivalentFormula :: Formula -> Property
prop_freeCountAlphaEquivalentFormula =
  withMaxSuccess 100000 . freeCountAlphaEquivalent

prop_freeCountAlphaEquivalentClause :: Clause -> Property
prop_freeCountAlphaEquivalentClause = freeCountAlphaEquivalent

prop_freeCountAlphaEquivalentLiteral :: Literal -> Property
prop_freeCountAlphaEquivalentLiteral = freeCountAlphaEquivalent

prop_freeCountAlphaEquivalentTerm :: Term -> Property
prop_freeCountAlphaEquivalentTerm = freeCountAlphaEquivalent


-- ** 'genAlphaEquivalent' produces alpha equivalent expressions

actuallyAlphaEquivalent :: (Show e, FirstOrder e) => e -> Property
actuallyAlphaEquivalent a =
  forAll (genAlphaEquivalent a) $ \b ->
    a ~= b

prop_actuallyAlphaEquivalentFormula :: Formula -> Property
prop_actuallyAlphaEquivalentFormula =
  withMaxSuccess 100000 . actuallyAlphaEquivalent

prop_actuallyAlphaEquivalentClause :: Clause -> Property
prop_actuallyAlphaEquivalentClause = actuallyAlphaEquivalent

prop_actuallyAlphaEquivalentLiteral :: Literal -> Property
prop_actuallyAlphaEquivalentLiteral = actuallyAlphaEquivalent

prop_actuallyAlphaEquivalentTerm :: Term -> Property
prop_actuallyAlphaEquivalentTerm = actuallyAlphaEquivalent


-- ** 'genAlphaInequivalent' produces alpha inequivalent expressions

actuallyAlphaInequivalent :: (Show e, FirstOrder e) => e -> Property
actuallyAlphaInequivalent a =
  length (vars a) > 1 ==>
    forAll (genAlphaInequivalent a) $ \b ->
      not (a ~= b)

prop_actuallyAlphaInequivalentFormula :: Formula -> Property
prop_actuallyAlphaInequivalentFormula =
  withMaxSuccess 50000 . actuallyAlphaInequivalent

prop_actuallyAlphaInequivalentClause :: Clause -> Property
prop_actuallyAlphaInequivalentClause = actuallyAlphaInequivalent

prop_actuallyAlphaInequivalentLiteral :: Literal -> Property
prop_actuallyAlphaInequivalentLiteral = actuallyAlphaInequivalent

prop_actuallyAlphaInequivalentTerm :: Term -> Property
prop_actuallyAlphaInequivalentTerm = actuallyAlphaInequivalent


-- * Free and bound variables

freeBoundVars :: FirstOrder e => e -> Property
freeBoundVars e = free e <> bound e === vars e

prop_freeBoundVarsFormula :: Formula -> Property
prop_freeBoundVarsFormula = freeBoundVars

prop_freeBoundVarsClause :: Clause -> Property
prop_freeBoundVarsClause = freeBoundVars

prop_freeBoundVarsLiteral :: Literal -> Property
prop_freeBoundVarsLiteral = freeBoundVars

prop_freeBoundVarsTerm :: Term -> Property
prop_freeBoundVarsTerm = freeBoundVars


-- * Alpha equivalence

-- ** Alpha equivalence is reflexive

alphaEquivalenceReflexivity :: FirstOrder e => e -> Property
alphaEquivalenceReflexivity e = property (e ~= e)

prop_alphaEquivalenceReflexivityFormula :: Formula -> Property
prop_alphaEquivalenceReflexivityFormula =
  withMaxSuccess 100000 . alphaEquivalenceReflexivity

prop_alphaEquivalenceReflexivityClause :: Clause -> Property
prop_alphaEquivalenceReflexivityClause = alphaEquivalenceReflexivity

prop_alphaEquivalenceReflexivityLiteral :: Literal -> Property
prop_alphaEquivalenceReflexivityLiteral = alphaEquivalenceReflexivity

prop_alphaEquivalenceReflexivityTerm :: Term -> Property
prop_alphaEquivalenceReflexivityTerm = alphaEquivalenceReflexivity


-- ** Alpha equivalence is symmetric

alphaEquivalenceSymmetry :: (Show e, FirstOrder e) => e -> Property
alphaEquivalenceSymmetry a =
  forAll (genAlphaEquivalent a) $ \b ->
    b ~= a

prop_alphaEquivalenceSymmetryFormula :: Formula -> Property
prop_alphaEquivalenceSymmetryFormula =
  withMaxSuccess 100000 . alphaEquivalenceSymmetry

prop_alphaEquivalenceSymmetryClause :: Clause -> Property
prop_alphaEquivalenceSymmetryClause = alphaEquivalenceSymmetry

prop_alphaEquivalenceSymmetryLiteral :: Literal -> Property
prop_alphaEquivalenceSymmetryLiteral = alphaEquivalenceSymmetry

prop_alphaEquivalenceSymmetryTerm :: Term -> Property
prop_alphaEquivalenceSymmetryTerm = alphaEquivalenceSymmetry


-- ** Alpha equivalence is transitive

alphaEquivalenceTransitivity :: (Show e, FirstOrder e) => e -> Property
alphaEquivalenceTransitivity a =
  forAll (genAlphaEquivalent a) $ \b ->
    forAll (genAlphaEquivalent b) $ \c ->
      a ~= c

prop_alphaEquivalenceTransitivityFormula :: Formula -> Property
prop_alphaEquivalenceTransitivityFormula =
  withMaxSuccess 100000 . alphaEquivalenceTransitivity

prop_alphaEquivalenceTransitivityClause :: Clause -> Property
prop_alphaEquivalenceTransitivityClause = alphaEquivalenceTransitivity

prop_alphaEquivalenceTransitivityLiteral :: Literal -> Property
prop_alphaEquivalenceTransitivityLiteral = alphaEquivalenceTransitivity

prop_alphaEquivalenceTransitivityTerm :: Term -> Property
prop_alphaEquivalenceTransitivityTerm = alphaEquivalenceTransitivity


-- * Simplification

-- ** Clauses

prop_simplifyClauseEliminatesNegatedConstants :: Clause -> Property
prop_simplifyClauseEliminatesNegatedConstants c =
  whenFail (print s) (isSimplifiedClause s)
    where s = simplifyClause c

isNegatedConstant :: Signed Literal -> Bool
isNegatedConstant = \case
  Signed Negative Constant{} -> True
  _ -> False

isSimplifiedClause :: Clause -> Bool
isSimplifiedClause (Literals ls) =
  not (any isNegatedConstant ls) &&
  FalsumLiteral `notElem` ls &&
  (ls == [TautologyLiteral] || TautologyLiteral `notElem` ls)

prop_simplifyClauses :: Clauses -> Property
prop_simplifyClauses cs =
  whenFail (print ss) (areSimplifiedClauses ss)
    where ss = simplifyClauses cs

areSimplifiedClauses :: Clauses -> Bool
areSimplifiedClauses (Clauses []) = True
areSimplifiedClauses (Clauses cs) =
  all isSimplifiedClause cs &&
  (cs == [EmptyClause] || EmptyClause `notElem` cs)


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
  where (==~) = (===) `on` simplifyClause

prop_simplifyIdempotentFormula :: Formula -> Property
prop_simplifyIdempotentFormula f = simplifyFormula f ==~ f
  where (==~) = (===) `on` simplifyFormula

prop_simplifyIdempotentLogicalExpression :: LogicalExpression -> Property
prop_simplifyIdempotentLogicalExpression e = simplify e ==~ e
  where (==~) = (===) `on` simplify

prop_simplifyIdempotentClauses :: Clauses -> Property
prop_simplifyIdempotentClauses cs = simplifyClauses cs ==~ cs
  where (==~) = (===) `on` simplifyClauses

prop_simplifyIdempotentTheorem :: Theorem -> Property
prop_simplifyIdempotentTheorem t = simplifyTheorem t ==~ t
  where (==~) = (===) `on` simplifyTheorem


-- * Conversions

prop_liftUnliftSignedLiteral :: Signed Literal -> Property
prop_liftUnliftSignedLiteral s =
  unliftSignedLiteral (liftSignedLiteral s) === Just s

prop_liftUnliftClause :: Clause -> Property
prop_liftUnliftClause c = unliftClause (liftClause c) ==~ Just c
  where (==~) = (===) `on` fmap simplifyClause

prop_liftUnliftContradiction :: (Show f, Eq f) => Contradiction f -> Property
prop_liftUnliftContradiction c =
  unliftContradiction (liftContradiction c) === Just c


-- * Codec

prop_codecClause :: Clause -> Property
prop_codecClause c = return c ~==~ decodeClause (encodeClause c)
  where (~==~) = (~~=) `on` fmap simplifyClause

prop_codecFormula :: Formula -> Property
prop_codecFormula f = return f ~==~ decodeFormula (encodeFormula f)
  where (~==~) = (~~=) `on` fmap simplifyFormula

prop_codec :: LogicalExpression -> Property
prop_codec e = return e ~==~ decode (encode e)
  where (~==~) = (~~=) `on` fmap simplify


-- * Runner

return []

main :: IO ()
main = do
  let args = stdArgs{maxSuccess=1000, maxDiscardRatio=50}
  success <- $forAllProperties (quickCheckWithResult args)
  unless success exitFailure
