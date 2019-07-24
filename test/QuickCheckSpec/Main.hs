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

substituteIdempotence :: (Eq e, Show e, FirstOrder e)
                      => Var -> Term -> e -> Property
substituteIdempotence v t e =
  not (v `occursIn` t) ==>
    substitute v t (substitute v t e) === substitute v t e

prop_substituteIdempotenceFormula :: Var -> Term -> Formula -> Property
prop_substituteIdempotenceFormula = substituteIdempotence

prop_substituteIdempotenceLiteral :: Var -> Term -> Literal -> Property
prop_substituteIdempotenceLiteral = substituteIdempotence

prop_substituteIdempotenceTerm :: Var -> Term -> Term -> Property
prop_substituteIdempotenceTerm = substituteIdempotence

substituteCommutativity :: (Eq e, Show e, FirstOrder e)
                        => Var -> Term -> Var -> Term -> e -> Property
substituteCommutativity v t w s e =
  v /= w && not (v `occursIn` s) && not (w `occursIn` t) ==>
    substitute v t (substitute w s e) === substitute w s (substitute v t e)

prop_substituteCommutativityFormula :: Var -> Term -> Var -> Term -> Formula -> Property
prop_substituteCommutativityFormula = substituteCommutativity

prop_substituteCommutativityLiteral :: Var -> Term -> Var -> Term -> Literal -> Property
prop_substituteCommutativityLiteral = substituteCommutativity

prop_substituteCommutativityTerm :: Var -> Term -> Var -> Term -> Term -> Property
prop_substituteCommutativityTerm = substituteCommutativity

substituteFixedPoint :: (Eq e, Show e, FirstOrder e)
                     => Var -> Term -> e -> Property
substituteFixedPoint v t e =
  not (v `freeIn` e) ==>
    substitute v t e === e

prop_substituteFixedPointFormula :: Var -> Term -> Formula -> Property
prop_substituteFixedPointFormula = substituteFixedPoint

prop_substituteFixedPointLiteral :: Var -> Term -> Literal -> Property
prop_substituteFixedPointLiteral = substituteFixedPoint

prop_substituteFixedPointTerm :: Var -> Term -> Term -> Property
prop_substituteFixedPointTerm = substituteFixedPoint

substituteElimination :: (Eq e, Show e, FirstOrder e)
                      => Var -> Term -> e -> Property
substituteElimination v t e =
  not (v `occursIn` t) ==>
    not (v `freeIn` substitute v t e)

prop_substituteEliminationFormula :: Var -> Term -> Formula -> Property
prop_substituteEliminationFormula = substituteElimination

prop_substituteEliminationLiteral :: Var -> Term -> Literal -> Property
prop_substituteEliminationLiteral = substituteElimination

prop_substituteEliminationTerm :: Var -> Term -> Term -> Property
prop_substituteEliminationTerm = substituteElimination


-- * Runner

return []

main :: IO Bool
main = $forAllProperties $ quickCheckWithResult stdArgs{maxSuccess=1000}
