Haskell interface to automated theorem provers
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

humansAreMortal, socratesIsHuman, socratesIsMortal :: Formula
humansAreMortal = forall $ \x -> human x ==> mortal x
socratesIsHuman = human socrates
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

`prove` runs a third-party automated first-order theorem prover [E](https://wwwlehre.dhbw-stuttgart.de/~sschulz/E/E.html) to contruct a proof of the syllogism. This is a proof by _refutation_, that is, contradiction is derived from negated conjecture.

```
λ: prove syllogism >>= pprint
Found a proof by refutation using E.
1. human(socrates) [axiom]
2. ∀ x . (human(x) => mortal(x)) [axiom]
3. mortal(socrates) [conjecture]
4. ￢mortal(socrates) [negated conjecture 3]
5. ∀ x . (￢human(x) ⋁ mortal(x)) [variable_rename 2]
6. mortal(x) ⋁ ￢human(x) [split_conjunct 5]
7. mortal(socrates) [paramodulation 6, 1]
8. ⟘ [cn 4, 7]
```
