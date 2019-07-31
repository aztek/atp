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

-- ** Substitution is idempotent

substituteIdempotence :: (Eq e, Show e, FirstOrder e)
                      => Substitution -> e -> Property
substituteIdempotence s@(v, t) e =
  not (v `occursIn` t) ==>
    substitute s (substitute s e) === substitute s e

prop_substituteIdempotenceFormula :: Substitution -> Formula -> Property
prop_substituteIdempotenceFormula = substituteIdempotence

prop_substituteIdempotenceLiteral :: Substitution -> Literal -> Property
prop_substituteIdempotenceLiteral = substituteIdempotence

prop_substituteIdempotenceTerm :: Substitution -> Term -> Property
prop_substituteIdempotenceTerm = substituteIdempotence

-- ** Substitution is commutative

substituteCommutativity :: (Eq e, Show e, FirstOrder e)
                        => Substitution -> Substitution -> e -> Property
substituteCommutativity s1@(v, t) s2@(w, s) e =
  v /= w && not (v `occursIn` s) && not (w `occursIn` t) ==>
    substitute s1 (substitute s2 e) === substitute s2 (substitute s1 e)

prop_substituteCommutativityFormula :: Substitution -> Substitution -> Formula -> Property
prop_substituteCommutativityFormula = substituteCommutativity

prop_substituteCommutativityLiteral :: Substitution -> Substitution -> Literal -> Property
prop_substituteCommutativityLiteral = substituteCommutativity

prop_substituteCommutativityTerm :: Substitution -> Substitution -> Term -> Property
prop_substituteCommutativityTerm = substituteCommutativity

-- ** Substitution has a fixed point

substituteFixedPoint :: (Eq e, Show e, FirstOrder e)
                     => Substitution -> e -> Property
substituteFixedPoint s@(v, _) e =
  not (v `freeIn` e) ==>
    substitute s e === e

prop_substituteFixedPointFormula :: Substitution -> Formula -> Property
prop_substituteFixedPointFormula = substituteFixedPoint

prop_substituteFixedPointLiteral :: Substitution -> Literal -> Property
prop_substituteFixedPointLiteral = substituteFixedPoint

prop_substituteFixedPointTerm :: Substitution -> Term -> Property
prop_substituteFixedPointTerm = substituteFixedPoint

-- ** Substitution can eliminate free variables

substituteElimination :: (Eq e, Show e, FirstOrder e)
                      => Substitution -> e -> Property
substituteElimination s@(v, t) e =
  not (v `occursIn` t) ==>
    not (v `freeIn` substitute s e)

prop_substituteEliminationFormula :: Substitution -> Formula -> Property
prop_substituteEliminationFormula = substituteElimination

prop_substituteEliminationLiteral :: Substitution -> Literal -> Property
prop_substituteEliminationLiteral = substituteElimination

prop_substituteEliminationTerm :: Substitution -> Term -> Property
prop_substituteEliminationTerm = substituteElimination


-- * Runner

return []

main :: IO Bool
main = $forAllProperties $ quickCheckWithResult stdArgs{maxSuccess=1000}
