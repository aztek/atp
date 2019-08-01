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

import qualified Data.Set as S (union)

import Test.QuickCheck (
    Property, (===), (==>),
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


-- * Runner

return []

main :: IO Bool
main = $forAllProperties $ quickCheckWithResult stdArgs{maxSuccess=1000}
