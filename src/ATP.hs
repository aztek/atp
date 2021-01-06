{-|
Module       : ATP
Description  : Interface to automated theorem provers.
Copyright    : (c) Evgenii Kotelnikov, 2019
License      : GPL-3
Maintainer   : evgeny.kotelnikov@gmail.com
Stability    : experimental

Express theorems in first-order logic and automatically prove them
using third-party reasoning tools.
-}

module ATP (
  -- * First-order logic
  -- $fol
  module ATP.FOL,

  -- * Pretty printing for formulas, theorems and proofs
  -- $pretty
  module ATP.Pretty.FOL,

  -- * Interface to automated theorem provers
  -- $prove
  module ATP.Prove,

  -- * Models of automated theorem provers
  -- $prover
  module ATP.Prover,

  -- * Error handling
  -- $error
  module ATP.Error
) where

import ATP.FOL
import ATP.Pretty.FOL
import ATP.Prove
import ATP.Prover
import ATP.Error

-- $fol
-- Consider the following classical logical syllogism.
--
-- /All humans are mortal. Socrates is a human. Therefore, Socrates is mortal./
--
-- We can formalize it in first-order logic as follows.
--
-- > human, mortal :: UnaryPredicate
-- > human = UnaryPredicate "human"
-- > mortal = UnaryPredicate "mortal"
-- >
-- > socrates :: Constant
-- > socrates = "socrates"
-- >
-- > humansAreMortal, socratesIsHuman, socratesIsMortal :: Formula
-- > humansAreMortal = forall $ \x -> human x ==> mortal x
-- > socratesIsHuman = human socrates
-- > socratesIsMortal = mortal socrates
-- >
-- > syllogism :: Theorem
-- > syllogism = [humansAreMortal, socratesIsHuman] |- socratesIsMortal

-- $pretty
-- 'pprint' pretty-prints theorems and proofs.
--
-- >>> pprint syllogism
-- Axiom 1. ∀ x . (human(x) => mortal(x))
-- Axiom 2. human(socrates)
-- Conjecture. mortal(socrates)

-- $prove
-- 'prove' runs a 'defaultProver' and parses the proof that it produces.
--
-- >>> prove syllogism >>= pprint
-- Found a proof by refutation.
-- 1. human(socrates) [axiom]
-- 2. ∀ x . (human(x) => mortal(x)) [axiom]
-- 3. mortal(socrates) [conjecture]
-- 4. ￢mortal(socrates) [negated conjecture 3]
-- 5. ∀ x . (￢human(x) ⋁ mortal(x)) [variable_rename 2]
-- 6. mortal(x) ⋁ ￢human(x) [split_conjunct 5]
-- 7. mortal(socrates) [paramodulation 6, 1]
-- 8. ⟘ [cn 4, 7]
--
-- The proof returned by the theorem prover is a directed acyclic graph of
-- logical inferences. Each logical 'Inference' is a step of the proof that
-- derives a conclusion from a set of premises using an inference 'Rule'.
-- The proof ends with a 'Contradiction' and therefore is a proof by
-- 'Refutation'.

-- $prover
-- By default 'prove' runs the E theorem prover ('eprover'). Currently,
-- 'eprover' and 'vampire' are supported.
--
-- 'proveUsing' runs a specified theorem prover.

-- $error
-- A theorem prover might not succeed to construct a proof. Therefore the result
-- of 'prove' is wrapped in the 'Partial' monad that represents a possible
-- 'Error', for example 'TimeLimitError' or 'ParsingError'.
