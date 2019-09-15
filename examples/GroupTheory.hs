{-# LANGUAGE OverloadedStrings #-}

{-|
Module       : GroupTheory
Description  : A theorem in group theory.
Copyright    : (c) Evgenii Kotelnikov, 2019
License      : GPL-3
Maintainer   : evgeny.kotelnikov@gmail.com
Stability    : experimental
-}

module GroupTheory where

import ATP


inverse :: UnaryFunction
inverse = unaryFunction "inverse"

(.*.) :: BinaryFunction
(.*.) = binaryFunction "mult"

e :: Constant
e = "e"

leftIdentity :: Formula
leftIdentity = forall $ \x -> e .*. x === x

leftInverse :: Formula
leftInverse = forall $ \x -> inverse x .*. x === e

associativity :: Formula
associativity = forall $ \x y z -> (x .*. y) .*. z === x .*. (y .*. z)

groupOfOrder2 :: Formula
groupOfOrder2 = forall $ \x -> x .*. x === e

commutativity :: Formula
commutativity = forall $ \x y -> x .*. y === y .*. x

theorem :: Theorem
theorem = [leftIdentity, leftInverse, associativity, groupOfOrder2] |- commutativity