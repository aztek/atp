{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}

{-|
Module       : UnitTests.Main
Description  : Basic unit tests.
Copyright    : (c) Evgenii Kotelnikov, 2019-2020
License      : GPL-3
Maintainer   : evgeny.kotelnikov@gmail.com
Stability    : experimental
-}

module UnitTests.Main (tests) where

import Distribution.TestSuite (Test(..), TestInstance(..),
                               Progress(..), Result(..))
import ATP
import ATP.Error (liftPartial)


-- * Helpers

uncurry3 :: (a -> b -> c -> d) -> (a, b, c) -> d
uncurry3 f (a, b, c) = f a b c

simpleTest :: String -> IO Progress -> Test
simpleTest nm progress = Test $ TestInstance {
  name      = nm,
  tags      = [],
  options   = [],
  setOption = const . const $ Left "not supported",
  run       = progress
}

testCase :: String -> IO Answer -> (Solution -> Result) -> Test
testCase nm answer testSolution = simpleTest nm r
  where
    r = fmap (Finished . testPartial . liftPartial . solution) answer
    testPartial = \case
      Left  e -> Error ("Failed to find a solution: " ++ show e)
      Right s -> testSolution s

expectSaturation :: Solution -> Result
expectSaturation = \case
  Saturation{} -> Pass
  Proof{} -> Error "Unexpected proof"

expectProof :: Solution -> Result
expectProof = \case
  Saturation{} -> Error "Unexpected saturation"
  Proof{} -> Pass


-- * Test data

emptyClause :: ClauseSet
emptyClause = ClauseSet [EmptyClause]

negated :: Theorem -> Theorem
negated (Theorem as c) = Theorem as (neg c)

syllogism :: Theorem
syllogism = [humansAreMortal, human "socrates"] |- mortal "socrates"
  where
    humansAreMortal = forall $ \x -> human x ==> mortal x
    human = UnaryPredicate "human"
    mortal = UnaryPredicate "mortal"

groupTheoryAxiom :: Theorem
groupTheoryAxiom = [leftIdentity, leftInverse, associativity, groupOfOrder2] |- commutativity
  where
    inverse = UnaryFunction "inverse"
    (.*.) = BinaryFunction "mult"
    leftIdentity  = forall $ \x -> "e" .*. x === x
    leftInverse   = forall $ \x -> inverse x .*. x === "e"
    associativity = forall $ \x y z -> (x .*. y) .*. z === x .*. (y .*. z)
    groupOfOrder2 = forall $ \x -> x .*. x === "e"
    commutativity = forall $ \x y -> x .*. y === y .*. x


-- * Test suite

tests :: IO [Test]
tests = return $ fmap (uncurry3 testCase) [
    ("E refutes an empty clause",       refute emptyClause,    expectProof),
    ("E saturates an empty clause set", refute (ClauseSet []), expectSaturation),

    ("E proves tautology", prove (Claim Tautology), expectProof),
    ("E saturates falsum", prove (Claim Falsum),    expectSaturation),

    ("E proves syllogism",            prove syllogism,        expectProof),
    ("E saturates negated syllogism", prove (negated syllogism), expectSaturation),

    ("E proves group theory axiom", prove groupTheoryAxiom, expectProof)
  ]
