{-# LANGUAGE OverloadedStrings #-}

{-|
Module       : GroupTheory
Description  : A theorem in group theory.
Copyright    : (c) Evgenii Kotelnikov, 2019-2021
License      : GPL-3
Maintainer   : evgeny.kotelnikov@gmail.com
Stability    : experimental

If all elements in a group have order 2, then the group is commutative.
-}

module GroupTheory where

import Prelude hiding ((*))

import ATP


inverse :: UnaryFunction
inverse = UnaryFunction "inverse"

(*) :: BinaryFunction
(*) = BinaryFunction "mult"

e :: Constant
e = "e"

leftIdentity :: Formula
leftIdentity = forall $ \x -> e * x === x

leftInverse :: Formula
leftInverse = forall $ \x -> inverse x * x === e

associativity :: Formula
associativity = forall $ \x y z -> (x * y) * z === x * (y * z)

groupOfOrder2 :: Formula
groupOfOrder2 = forall $ \x -> x * x === e

commutativity :: Formula
commutativity = forall $ \x y -> x * y === y * x

theorem :: Theorem
theorem = [leftIdentity, leftInverse, associativity, groupOfOrder2] |- commutativity
