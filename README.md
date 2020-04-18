Haskell bindings to automated theorem provers
===

[![Build Status](https://travis-ci.org/aztek/atp.svg?branch=master)](https://travis-ci.org/aztek/atp)

Express theorems in first-order logic and automatically prove them using third-party reasoning tools.

> All humans are mortal.
>
> Socrates is a human.
>
> Therefore, Socrates is mortal.

```haskell
import ATP

human, mortal :: UnaryPredicate
human = UnaryPredicate "human"
mortal = UnaryPredicate "mortal"

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
```

`pprint` pretty-prints theorems and proofs.

```
λ: pprint syllogism
Axiom 1. ∀ x . (human(x) => mortal(x))
Axiom 2. human(socrates)
Conjecture. mortal(socrates)
```

`prove` runs a third-party automated first-order theorem prover [E](https://wwwlehre.dhbw-stuttgart.de/~sschulz/E/E.html) to contruct a proof of the syllogism.

```
λ: prove syllogism >>= pprint
Found a proof by contradiction using E.
11. ⟘ [cn 9, 10]
10. mortal(socrates) [pm 7, 8]
9. ￢mortal(socrates) [split_conjunct 6]
8. human(socrates) [split_conjunct 3]
7. mortal(x) ⋁ ￢human(x) [split_conjunct 5]
6. ￢mortal(socrates) [fof_simplification 4]
5. ∀ x . (￢human(x) ⋁ mortal(x)) [variable_rename 2]
4. ￢mortal(socrates) [negated conjecture 1]
3. human(socrates) [axiom]
2. ∀ x . (human(x) => mortal(x)) [axiom]
1. mortal(socrates) [conjecture]
```
