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


-- * Helpers

simpleTest :: String -> IO Progress -> Test
simpleTest nm progress = Test $ TestInstance {
  name      = nm,
  tags      = [],
  options   = [],
  setOption = const . const $ Left "not supported",
  run       = progress
}

testCase :: Prover -> String ->
            (Either Error Solution -> Result) ->
            Either Clauses Theorem -> Test
testCase p nm testAnswer input = simpleTest testName progress
  where
    testName = show (vendor p) ++ " " ++ nm
    progress = fmap (Finished . testAnswer . liftPartial) solution
    solution = case input of
                 Left cs -> refuteWith opts cs
                 Right t -> proveWith  opts t
    opts = defaultOptions{prover=p, timeLimit=5}

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

expectTimLimitError :: Either Error Solution -> Result
expectTimLimitError = \case
  Left TimeLimitError -> Pass
  Left  e -> Error $ "Unexpected error " ++ show e
  Right _ -> Error "Unexpected solution"


-- * Test data

emptyClause :: Clauses
emptyClause = Clauses [EmptyClause]

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
tests = return [testCase p n t i | (n, t, i) <- cases, p <- provers]
  where
    provers = [eprover, vampire]
    cases = [
        ("refutes an empty clause",       expectProof,      Left emptyClause),
        ("saturates an empty clause set", expectSaturation, Left (Clauses [])),

        ("proves tautology", expectProof,      Right (Claim Tautology)),
        ("saturates falsum", expectSaturation, Right (Claim Falsum)),

        ("proves syllogism",            expectProof,      Right syllogism),
        ("saturates negated syllogism", expectSaturation, Right (negated syllogism)),

        ("proves group theory axiom", expectProof,         Right groupTheoryAxiom),
        ("reached time limit",        expectTimLimitError, Right (negated groupTheoryAxiom))
      ]
