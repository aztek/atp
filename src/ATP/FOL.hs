{-|
Module       : ATP.FOL
Description  : Unsorted first-order logic.
Copyright    : (c) Evgenii Kotelnikov, 2019-2020
License      : GPL-3
Maintainer   : evgeny.kotelnikov@gmail.com
Stability    : experimental

Data structures that represent formulas and theorems in first-order logic,
and smart constructors for them.

Consider the following classical logical syllogism.

/All humans are mortal. Socrates is a human. Therefore, Socrates is mortal./

We can formalize it in first-order logic and express in Haskell as follows.

> human, mortal :: UnaryPredicate
> human = UnaryPredicate "human"
> mortal = UnaryPredicate "mortal"
>
> socrates :: Constant
> socrates = "socrates"
>
> humansAreMortal :: Formula
> humansAreMortal = forall $ \x -> human x ==> mortal x
>
> socratesIsHuman :: Formula
> socratesIsHuman = human socrates
>
> socratesIsMortal :: Formula
> socratesIsMortal = mortal socrates
>
> syllogism :: Theorem
> syllogism = [humansAreMortal, socratesIsHuman] |- socratesIsMortal
-}

module ATP.FOL (
  module ATP.FirstOrder.Core,
  module ATP.FirstOrder.Smart,
  module ATP.FirstOrder.Simplification,
  module ATP.FirstOrder.Occurrence,
  module ATP.FirstOrder.Conversion,
  module ATP.FirstOrder.Theorem
) where

import ATP.FirstOrder.Core
import ATP.FirstOrder.Smart
import ATP.FirstOrder.Simplification
import ATP.FirstOrder.Occurrence
import ATP.FirstOrder.Conversion
import ATP.FirstOrder.Theorem
