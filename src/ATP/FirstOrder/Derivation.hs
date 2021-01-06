{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE CPP #-}

{-|
Module       : ATP.FirstOrder.Derivation
Description  : Derivations in first-order logic.
Copyright    : (c) Evgenii Kotelnikov, 2019-2021
License      : GPL-3
Maintainer   : evgeny.kotelnikov@gmail.com
Stability    : experimental
-}

module ATP.FirstOrder.Derivation (
  -- * Proofs
  Rule(..),
  RuleName(..),
  ruleName,
  Inference(..),
  antecedents,
  Contradiction(..),
  Sequent(..),
  Derivation(..),
  addSequent,
  breadthFirst,
  labeling,
  Refutation(..),
  Solution(..)
) where

import Data.Foldable (toList)
import Data.Function (on)
import Data.List (sortBy)
import qualified Data.Map as M (fromList, insert, toList)
import Data.Map (Map, (!))
#if !MIN_VERSION_base(4, 11, 0)
import Data.Semigroup (Semigroup)
#endif
import Data.String (IsString(..))
import Data.Text (Text)

import ATP.FirstOrder.Core


-- * Proofs

-- | The inference rule.
data Rule f
  = Axiom
  | Conjecture
  | NegatedConjecture  f
  | Flattening         f
  | Skolemisation      f
  | EnnfTransformation f
  | NnfTransformation  f
  | Clausification     f
  | TrivialInequality  f
  | Superposition         f f
  | Resolution            f f
  | Paramodulation        f f
  | SubsumptionResolution f f
  | ForwardDemodulation   f f
  | BackwardDemodulation  f f
  | AxiomOfChoice
  | Unknown        [f]
  | Other RuleName [f]
  deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

-- | The name of an inference rule.
newtype RuleName = RuleName { unRuleName :: Text }
  deriving (Show, Eq, Ord, IsString)

-- | The name of the given inference rule.
--
-- >>> unRuleName (ruleName AxiomOfChoice)
-- "axiom of choice"
ruleName :: Rule f -> RuleName
ruleName = \case
  Axiom{}                 -> "axiom"
  Conjecture{}            -> "conjecture"
  NegatedConjecture{}     -> "negated conjecture"
  Flattening{}            -> "flattening"
  Skolemisation{}         -> "skolemisation"
  EnnfTransformation{}    -> "ennf transformation"
  NnfTransformation{}     -> "nnf transformation"
  Clausification{}        -> "clausification"
  TrivialInequality{}     -> "trivial inequality"
  Superposition{}         -> "superposition"
  Resolution{}            -> "resolution"
  Paramodulation{}        -> "paramodulation"
  SubsumptionResolution{} -> "subsumption resolution"
  ForwardDemodulation{}   -> "forward demodulation"
  BackwardDemodulation{}  -> "backward demodulation"
  AxiomOfChoice{}         -> "axiom of choice"
  Unknown{}               -> "unknown"
  Other name _            -> name

-- | A logical inference is an expression of the form
--
-- > A_1 ... A_n
-- > ----------- R,
-- >     C
--
-- where each of @A_1@, ... @A_n@ (called the 'antecedents'), and @C@
-- (called the 'consequent') are formulas and @R@ is an inference 'Rule'.
data Inference f = Inference {
  inferenceRule :: Rule f,
  consequent :: LogicalExpression
} deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

-- | The antecedents of an inference.
antecedents :: Inference f -> [f]
antecedents = toList

-- | Contradiction is a special case of an inference that has the logical falsum
-- as the consequent.
newtype Contradiction f = Contradiction (Rule f)
  deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

-- | A sequent is a logical inference, annotated with a label.
-- Linked sequents form derivations.
data Sequent f = Sequent f (Inference f)
  deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

sequentMap :: Ord f => [Sequent f] -> Map f (Inference f)
sequentMap ss = M.fromList [(f, e) | Sequent f e <- ss]

-- | Construct a mapping between inference labels and their correspondent
-- formulas.
labeling :: Ord f => [Sequent f] -> Map f LogicalExpression
labeling = fmap consequent . sequentMap

-- | A derivation is a directed asyclic graph of logical inferences.
-- In this graph nodes are formulas and edges are inference rules.
-- The type parameter @f@ is used to label and index the nodes.
newtype Derivation f = Derivation (Map f (Inference f))
  deriving (Show, Eq, Ord, Semigroup, Monoid)

-- | Attach a sequent to a derivation.
addSequent :: Ord f => Derivation f -> Sequent f -> Derivation f
addSequent (Derivation m) (Sequent f i) = Derivation (M.insert f i m)

fromDerivation :: Derivation f -> [Sequent f]
fromDerivation (Derivation m) = fmap (uncurry Sequent) (M.toList m)

-- | Traverse the given derivation breadth-first and produce a list of sequents.
breadthFirst :: Ord f => Derivation f -> [Sequent f]
breadthFirst d = sortBy (compare `on` criteria) (fromDerivation d)
  where criteria (Sequent l (Inference r f)) = (distances d ! l, r, f)

distances :: Ord f => Derivation f -> Map f Integer
distances (Derivation m) = fmap distance m
  where
    distance i
      | null (antecedents i) = 0
      | otherwise = 1 + maximum (fmap (\a -> distance (m ! a)) (antecedents i))

-- | A refutation is a special case of a derivation that results in a
-- contradiction. A successful proof produces by an automated theorem prover
-- is a proof by refutation.
data Refutation f = Refutation (Derivation f) (Contradiction f)
  deriving (Show, Eq, Ord)

-- | The solution produced by an automated first-order theorem prover.
data Solution
  = Saturation (Derivation Integer)
  -- ^ A theorem can be disproven if the prover constructs a saturated set of
  -- first-order clauses.
  | Proof (Refutation Integer)
  -- ^ A theorem can be proven if the prover derives contradiction (the empty
  -- clause) from the set of axioms and the negated conjecture.
  deriving (Show, Eq, Ord)
