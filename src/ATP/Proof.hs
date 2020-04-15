{-# LANGUAGE DeriveFunctor, DeriveTraversable, DeriveFoldable #-}
{-# LANGUAGE LambdaCase #-}

{-|
Module       : ATP.Proof
Description  : Proofs of theorems.
Copyright    : (c) Evgenii Kotelnikov, 2019
License      : GPL-3
Maintainer   : evgeny.kotelnikov@gmail.com
Stability    : experimental
-}

module ATP.Proof (
  Inference(..),
  sequents,
  antecedents,
  consequent,
  Derivation(..),
  Refutation(..),
  Proof(..),
  derivations,
  labeling
) where

import Data.Foldable (toList)
import Data.List.NonEmpty (NonEmpty(..))
import qualified Data.Map as M (fromList)
import Data.Map (Map)
import Data.Text (Text)

import ATP.FOL
import ATP.Prover


-- | A logical inference is an expression of the form
--
-- > A_1 ... A_n
-- > ----------- R,
-- >     C
--
-- where each of @A_1@, ... @A_n@ (called antecedents), and @C@
-- (called consequent) are formulas and @R@ is an inference rule.
--
-- Each of the constructors of 'Inference' represents a recognized inference
-- rule.
data Inference f
  = Axiom      f
  | Conjecture f
  | NegatedConjecture  f f
  | Flattening         f f
  | Skolemisation      f f
  | EnnfTransformation f f
  | NnfTransformation  f f
  | Clausification     f f
  | TrivialInequality  f f
  | Superposition         f f f
  | Resolution            f f f
  | SubsumptionResolution f f f
  | ForwardDemodulation   f f f
  | BackwardDemodulation  f f f
  | Unknown    [f] f
  | Other Text [f] f
  deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

-- | The sequents involved in an inference - the list of antecedents and the
-- consequent.
sequents :: Inference f -> ([f], f)
sequents = \case
  Axiom      f -> ([], f)
  Conjecture f -> ([], f)
  NegatedConjecture  f g -> ([f], g)
  Flattening         f g -> ([f], g)
  Skolemisation      f g -> ([f], g)
  EnnfTransformation f g -> ([f], g)
  NnfTransformation  f g -> ([f], g)
  Clausification     f g -> ([f], g)
  TrivialInequality  f g -> ([f], g)
  Superposition         f g h -> ([f, g], h)
  Resolution            f g h -> ([f, g], h)
  SubsumptionResolution f g h -> ([f, g], h)
  ForwardDemodulation   f g h -> ([f, g], h)
  BackwardDemodulation  f g h -> ([f, g], h)
  Unknown fs g -> (fs, g)
  Other _ fs g -> (fs, g)

-- | The list of antecedents of an inference.
antecedents :: Inference f -> [f]
antecedents = fst . sequents

-- | The consequent of an inference.
consequent :: Inference f -> f
consequent = snd . sequents

data Derivation l = Derivation (Inference l) LogicalExpression
  deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

data Refutation l = Refutation (Inference l) [Derivation l]
  deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

-- | List all derivations that lead to the refutation.
derivations :: Refutation l -> NonEmpty (Derivation l)
derivations (Refutation i ds) = Derivation i (Clause EmptyClause) :| ds

-- | Construct a mapping between inference labels and their correspondent
-- formulas.
labeling :: Ord l => Refutation l -> Map l LogicalExpression
labeling = M.fromList . toList
         . fmap (\(Derivation i f) -> (consequent i, f))
         . derivations

-- | The proof by refutation with additional meta information such as which
-- prover found it.
data Proof = Proof {
  proofMeta :: Prover,
  refutation :: Refutation Integer
} deriving (Show, Eq, Ord)
