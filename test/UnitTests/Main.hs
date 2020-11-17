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
import ATP.Error (Error(..), liftPartial)


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

testCase :: String -> (Either Error Solution -> Result) -> IO Answer -> Test
testCase nm testAnswer = simpleTest nm
                       . fmap (Finished . testAnswer . liftPartial . solution)

expectSolution :: (Solution -> Result) -> Either Error Solution -> Result
expectSolution testSolution = \case
  Left  e -> Error ("Failed to find a solution: " ++ show e)
  Right s -> testSolution s

expectSaturation :: Either Error Solution -> Result
expectSaturation = expectSolution $ \case
  Saturation{} -> Pass
  Proof{} -> Error "Unexpected proof"

expectProof :: Either Error Solution -> Result
expectProof = expectSolution $ \case
  Saturation{} -> Error "Unexpected saturation"
  Proof{} -> Pass

expectTimeout :: Either Error Solution -> Result
expectTimeout = \case
  Left Timeout -> Pass
  Left  e -> Error $ "Unexpected error " ++ show e
  Right _ -> Error "Unexpected solution"


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
    ("E refutes an empty clause",       expectProof,      refute emptyClause),
    ("E saturates an empty clause set", expectSaturation, refute (ClauseSet [])),

    ("E proves tautology", expectProof,      prove (Claim Tautology)),
    ("E saturates falsum", expectSaturation, prove (Claim Falsum)),

    ("E proves syllogism",            expectProof,      prove syllogism),
    ("E saturates negated syllogism", expectSaturation, prove (negated syllogism)),

    ("E proves group theory axiom", expectProof,   prove groupTheoryAxiom),
    ("E reached time limit",        expectTimeout, proveWith defaultOptions{timeLimit=1} (negated groupTheoryAxiom))
  ]
