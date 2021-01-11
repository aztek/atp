# Haskell interface to automated theorem provers

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

(See [examples](./tree/master/examples) for more.)

`pprint` pretty-prints theorems and proofs.

```
λ: pprint syllogism
Axiom 1. ∀ x . (human(x) => mortal(x))
Axiom 2. human(socrates)
Conjecture. mortal(socrates)
```

`prove` runs a third-party automated first-order theorem prover [E](https://wwwlehre.dhbw-stuttgart.de/~sschulz/E/E.html) to construct a proof of the syllogism.

```
λ: prove syllogism >>= pprint
Found a proof by refutation.
1. human(socrates) [axiom]
2. ∀ x . (human(x) => mortal(x)) [axiom]
3. mortal(socrates) [conjecture]
4. ￢mortal(socrates) [negated conjecture 3]
5. ∀ x . (￢human(x) ⋁ mortal(x)) [variable_rename 2]
6. mortal(x) ⋁ ￢human(x) [split_conjunct 5]
7. mortal(socrates) [paramodulation 6, 1]
8. ⟘ [cn 4, 7]
```

The proof returned by the theorem prover is a directed acyclic graph of logical inferences. Each logical inference is a step of the proof that derives a conclusion from zero or more premises using one of the predefined inference rules. The proof starts with negating the conjecture (step 4) and ends with a contradiction (step 8) and therefore is a proof by _refutation_.

`proveUsing` runs a given theorem prover, currently supported are [E](https://wwwlehre.dhbw-stuttgart.de/~sschulz/E/E.html) and [Vampire](https://vprover.github.io/). `proveUsing vampire syllogism` runs Vampire that finds a proof that is very similar to the one above.
