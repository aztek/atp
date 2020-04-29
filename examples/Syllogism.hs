{-# LANGUAGE OverloadedStrings #-}

{-|
Module       : Syllogism
Description  : A classical logical syllogism.
Copyright    : (c) Evgenii Kotelnikov, 2019
License      : GPL-3
Maintainer   : evgeny.kotelnikov@gmail.com
Stability    : experimental

All humans are mortal.
Socrates is a human.
Therefore, Socrates is mortal.
-}

module Syllogism where

import ATP


human, mortal :: UnaryPredicate
human = UnaryPredicate "human"
mortal = UnaryPredicate "mortal"

socrates :: Constant
socrates = "socrates"

humansAreMortal, socratesIsHuman, socratesIsMortal :: Formula
humansAreMortal = forall $ \x -> human x ==> mortal x
socratesIsHuman = human socrates
socratesIsMortal = mortal socrates

syllogism :: Theorem
syllogism = [humansAreMortal, socratesIsHuman] |- socratesIsMortal
