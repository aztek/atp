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

import Data.List (nub)
import qualified Data.Map as M (elems)
import Data.Maybe (isJust, fromJust)
import qualified Data.Set as S (union)

import Test.QuickCheck (
    Property, (===), (==>), whenFail, counterexample,
    forAllProperties, quickCheckWithResult, stdArgs, Args(..)
  )

import ATP.FOL hiding ((===), (==>))

import QuickCheckSpec.Generators ()


-- * Free and bound variables

freeBoundVars :: (Eq e, Show e, FirstOrder e) => e -> Property
freeBoundVars e = free e `S.union` bound e === vars e

prop_freeBoundVarsFormula :: Formula -> Property
prop_freeBoundVarsFormula = freeBoundVars

prop_freeBoundVarsLiteral :: Literal -> Property
prop_freeBoundVarsLiteral = freeBoundVars

prop_freeBoundVarsTerm :: Term -> Property
prop_freeBoundVarsTerm = freeBoundVars


-- * Substitutions

-- ** Some substitutions are idempotent

substituteIdempotence :: (Eq e, Show e, FirstOrder e) => Substitution -> e -> Property
substituteIdempotence s e =
  eliminatesVariables s ==> substitute s (substitute s e) === substitute s e

prop_substituteIdempotenceFormula :: Substitution -> Formula -> Property
prop_substituteIdempotenceFormula = substituteIdempotence

prop_substituteIdempotenceLiteral :: Substitution -> Literal -> Property
prop_substituteIdempotenceLiteral = substituteIdempotence

prop_substituteIdempotenceTerm :: Substitution -> Term -> Property
prop_substituteIdempotenceTerm = substituteIdempotence

-- ** Some substitutions are commutative

substituteCommutativity :: (Eq e, Show e, FirstOrder e)
                        => Substitution -> Substitution -> e -> Property
substituteCommutativity s s' e =
  independent s s' ==>
    substitute s (substitute s' e) === substitute s' (substitute s e)

prop_substituteCommutativityFormula :: Substitution -> Substitution -> Formula -> Property
prop_substituteCommutativityFormula = substituteCommutativity

prop_substituteCommutativityLiteral :: Substitution -> Substitution -> Literal -> Property
prop_substituteCommutativityLiteral = substituteCommutativity

prop_substituteCommutativityTerm :: Substitution -> Substitution -> Term -> Property
prop_substituteCommutativityTerm = substituteCommutativity

-- ** Some substitutions have a fixed point

substituteFixedPoint :: (Eq e, Show e, FirstOrder e) => Substitution -> e -> Property
substituteFixedPoint s e = not (effective s e) ==> substitute s e === e

prop_substituteFixedPointFormula :: Substitution -> Formula -> Property
prop_substituteFixedPointFormula = substituteFixedPoint

prop_substituteFixedPointLiteral :: Substitution -> Literal -> Property
prop_substituteFixedPointLiteral = substituteFixedPoint

prop_substituteFixedPointTerm :: Substitution -> Term -> Property
prop_substituteFixedPointTerm = substituteFixedPoint

-- ** Some substitution can eliminate free variables

substituteElimination :: (Eq e, Show e, FirstOrder e)
                      => Var -> Substitution -> e -> Property
substituteElimination v s e =
  eliminatesVariable v s ==> not (v `freeIn` substitute s e)

prop_substituteEliminationFormula :: Var -> Substitution -> Formula -> Property
prop_substituteEliminationFormula = substituteElimination

prop_substituteEliminationLiteral :: Var -> Substitution -> Literal -> Property
prop_substituteEliminationLiteral = substituteElimination

prop_substituteEliminationTerm :: Var -> Substitution -> Term -> Property
prop_substituteEliminationTerm = substituteElimination

-- ** Some substitutions are only effective once

substituteEffective :: (Eq e, Show e, FirstOrder e) => Substitution -> e -> Property
substituteEffective s e =
  eliminatesVariables s ==> not $ effective s (substitute s e)

prop_substituteEffectiveFormula :: Substitution -> Formula -> Property
prop_substituteEffectiveFormula = substituteEffective

prop_substituteEffectiveLiteral :: Substitution -> Literal -> Property
prop_substituteEffectiveLiteral = substituteEffective

prop_substituteEffectiveTerm :: Substitution -> Term -> Property
prop_substituteEffectiveTerm = substituteEffective


-- * Alpha conversions

-- ** Renamings are injective

alphaInjective :: (Eq e, Show e, FirstOrder e) => e -> e -> Property
alphaInjective a b =
  whenFail (print $ alpha a b) $
    isJust (alpha a b) ==> injective (fromJust $ alpha a b)
  where
    injective r = nub (M.elems r) == M.elems r

prop_alphaInjectiveFormula :: Formula -> Formula -> Property
prop_alphaInjectiveFormula = alphaInjective

prop_alphaInjectiveLiteral :: Literal -> Literal -> Property
prop_alphaInjectiveLiteral = alphaInjective

prop_alphaInjectiveTerm :: Term -> Term -> Property
prop_alphaInjectiveTerm = alphaInjective

-- ** Alpha conversion is a renaming

alphaRename :: (Eq e, Show e, FirstOrder e) => e -> e -> Property
alphaRename a b =
  whenFail (print $ alpha a b) $
    isJust (alpha a b) ==> rename (fromJust $ alpha a b) a === b

prop_alphaRenameFormula :: Formula -> Formula -> Property
prop_alphaRenameFormula = alphaRename

prop_alphaRenameLiteral :: Literal -> Literal -> Property
prop_alphaRenameLiteral = alphaRename

prop_alphaRenameTerm :: Term -> Term -> Property
prop_alphaRenameTerm = alphaRename

-- ** Alpha equivalence is symmetric

alphaEquivalenceSymmetry :: (Eq e, Show e, FirstOrder e) => e -> Property
alphaEquivalenceSymmetry e =
  whenFail (print $ alpha e e) $
    e `alphaEquivalent` e

prop_alphaEquivalenceSymmetryFormula :: Formula -> Property
prop_alphaEquivalenceSymmetryFormula = alphaEquivalenceSymmetry

prop_alphaEquivalenceSymmetryLiteral :: Literal -> Property
prop_alphaEquivalenceSymmetryLiteral = alphaEquivalenceSymmetry

prop_alphaEquivalenceSymmetryTerm :: Term -> Property
prop_alphaEquivalenceSymmetryTerm = alphaEquivalenceSymmetry

-- ** Alpha equivalence is reflexive

alphaEquivalenceReflexivity :: (Eq e, Show e, FirstOrder e) => e -> e -> Property
alphaEquivalenceReflexivity a b =
  whenFail (print $ alpha a b) $
    whenFail (print $ alpha b a) $
      a `alphaEquivalent` b == b `alphaEquivalent` a

prop_alphaEquivalenceReflexivityFormula :: Formula -> Formula -> Property
prop_alphaEquivalenceReflexivityFormula = alphaEquivalenceReflexivity

prop_alphaEquivalenceReflexivityLiteral :: Literal -> Literal -> Property
prop_alphaEquivalenceReflexivityLiteral = alphaEquivalenceReflexivity

prop_alphaEquivalenceReflexivityTerm :: Term -> Term -> Property
prop_alphaEquivalenceReflexivityTerm = alphaEquivalenceReflexivity

-- ** Alpha equivalence is transitive

alphaEquivalenceTransitivity :: (Eq e, Show e, FirstOrder e)
                             => e -> e -> e -> Property
alphaEquivalenceTransitivity a b c =
  whenFail (print $ alpha a b) $
    whenFail (print $ alpha b c) $
      whenFail (print $ alpha a c) $
        a `alphaEquivalent` b ==>
          b `alphaEquivalent` c ==>
            a `alphaEquivalent` c

prop_alphaEquivalenceTransitivityFormula :: Formula -> Formula -> Formula -> Property
prop_alphaEquivalenceTransitivityFormula = alphaEquivalenceTransitivity

prop_alphaEquivalenceTransitivityLiteral :: Literal -> Literal -> Literal -> Property
prop_alphaEquivalenceTransitivityLiteral = alphaEquivalenceTransitivity

prop_alphaEquivalenceTransitivityTerm :: Term -> Term -> Term -> Property
prop_alphaEquivalenceTransitivityTerm = alphaEquivalenceTransitivity


-- * Simplification

prop_simplifyIdempotent :: Formula -> Property
prop_simplifyIdempotent f = simplify (simplify f) === simplify f


-- * Runner

return []

main :: IO Bool
main = $forAllProperties $ quickCheckWithResult stdArgs{maxSuccess=1000}
