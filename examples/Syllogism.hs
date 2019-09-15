{-# LANGUAGE OverloadedStrings #-}

{-|
Module       : Syllogism
Description  : A classical logical syllogism.
Copyright    : (c) Evgenii Kotelnikov, 2019
License      : GPL-3
Maintainer   : evgeny.kotelnikov@gmail.com
Stability    : experimental
-}

module Syllogism where

import ATP


human, mortal :: UnaryPredicate
human = unaryPredicate "human"
mortal = unaryPredicate "mortal"

socrates :: Constant
socrates = "socrates"

humansAreMortal :: Formula
humansAreMortal = forall $ \x -> human x ==> mortal x

socratesIsHuman :: Formula
socratesIsHuman = human socrates

socratesIsMortal :: Formula
socratesIsMortal = mortal socrates

syllogism :: Theorem
syllogism = [humansAreMortal, socratesIsHuman] |- socratesIsMortal
