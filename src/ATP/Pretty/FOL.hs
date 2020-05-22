{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleInstances #-}

module ATP.Pretty.FOL (
  Pretty(..),
  pprint,
  hprint
) where

import Control.Applicative (liftA2)
import Control.Monad (foldM)
import Data.Char (digitToInt)
import Data.Foldable (toList)
import Data.Functor (($>))
import Data.List (genericIndex, find)
import Data.List.NonEmpty (NonEmpty(..), nonEmpty)
import Data.Map (Map, (!))
import Data.Text as T (unpack)
import System.IO (Handle)

import Text.PrettyPrint.ANSI.Leijen hiding ((<$>))

import ATP.Internal.Enumeration

import ATP.FOL
import ATP.Proof
import ATP.Prover (Prover(..))


-- * Helper functions

-- | Pretty print to the standard output.
pprint :: Pretty a => a -> IO ()
pprint = putDoc . pretty

-- | Pretty print to an IO handle.
hprint :: Pretty a => Handle -> a -> IO ()
hprint h = hPutDoc h . pretty


-- * Pretty printer for formulas

prettyVar :: Var -> Doc
prettyVar v = cyan . text $ genericIndex variables (abs v)
  where
    variables :: [String]
    variables = liftA2 prime [0..] ["v", "x", "y", "z", "t"]

    prime :: Integer -> String -> String
    prime n w = letter ++ index
      where
        letter = if v >= 0 then w  else w ++ "′"
        index  = if n == 0 then "" else fmap ("₀₁₂₃₄₅₆₇₈₉" !!) (digits n)
        digits = fmap digitToInt . show

prettySymbol :: Symbol -> Doc
prettySymbol = text . unpack

prettyFunction, prettyPredicate :: Symbol -> Doc
prettyFunction  = prettySymbol
prettyPredicate = prettySymbol

sepBy :: Doc -> NonEmpty Doc -> Doc
sepBy s = foldl1 (\a b -> a <+> s <+> b)

commaSep :: NonEmpty Doc -> Doc
commaSep (d :| ds) = align $ d <> mconcat (fmap (comma <+>) ds)

prettyApplication :: Doc -> [Doc] -> Doc
prettyApplication s as
  | Just as' <- nonEmpty as = s <> parens (commaSep as')
  | otherwise = s

prettyParens :: Pretty e => (e -> Bool) -> e -> Doc
prettyParens simple e
  | simple e  = pretty e
  | otherwise = parens (pretty e)

instance Pretty Term where
  pretty = \case
    Variable v    -> prettyVar v
    Function f ts -> prettyApplication (prettyFunction f) (fmap pretty ts)

instance Pretty Literal where
  pretty = \case
    Constant True  -> blue "⟙"
    Constant False -> blue "⟘"
    Predicate p ts -> prettyApplication (prettyPredicate p) (fmap pretty ts)
    Equality a b   -> pretty a <+> "=" <+> pretty b

instance Pretty (Signed Literal) where
  pretty = \case
    Signed Negative (Equality a b) -> pretty a <+> "!=" <+> pretty b
    Signed Negative l -> blue "￢" <> pretty l
    Signed Positive l -> pretty l

instance Pretty Clause where
  pretty (Literals ls) = case nonEmpty ls of
    Nothing  -> pretty (Constant False)
    Just nls -> sepBy (pretty Or) (fmap pretty nls)

instance Pretty Connective where
  pretty = blue . \case
    And        -> "⋀"
    Or         -> "⋁"
    Implies    -> "=>"
    Equivalent -> "<=>"
    Xor        -> "<~>"

instance Pretty Quantifier where
  pretty = \case
    Forall -> "∀"
    Exists -> "∃"

instance Pretty Formula where
  pretty = \case
    Atomic l -> pretty l
    Negate (Atomic (Equality a b)) -> pretty a <+> "!=" <+> pretty b
    Negate f -> blue "￢" <> prettyParens unitary f
    Connected  c f g -> prettyParens (under c) f <+> pretty c
                    <+> prettyParens (under c) g
    Quantified q v f -> pretty q <+> prettyVar v <+> dot
                    <+> prettyParens unitary f

unitary :: Formula -> Bool
unitary = \case
  Atomic{}     -> True
  Negate{}     -> True
  Connected{}  -> False
  Quantified{} -> True

under :: Connective -> Formula -> Bool
under c = \case
  Connected c' _ _ | c == c' && isAssociative c -> True
  Quantified{} -> False
  f -> unitary f

instance Pretty LogicalExpression where
  pretty = \case
    Clause  c -> pretty c
    Formula f -> pretty f


-- * Pretty printer for theorems

instance Pretty Theorem where
  pretty = \case
    Theorem as c -> vsep (zipWith axiom [1..] as ++ [conclusion c]) <> line
      where
        axiom i = sequent ("Axiom" <+> integer i)
        conclusion = sequent "Conjecture"
        sequent h f = bold (h <> dot) <+> pretty f


-- * Pretty printer for proofs

instance Pretty l => Pretty (Rule l) where
  pretty rule = prettyRuleTag rule <> case nonEmpty (toList rule) of
    Just as -> space <> commaSep (fmap (bold . pretty) as)
    Nothing -> empty

prettyRuleTag :: Rule l -> Doc
prettyRuleTag = \case
  Conjecture{}            -> yellow "conjecture"
  NegatedConjecture{}     -> yellow "negated conjecture"
  Axiom{}                 -> yellow "axiom"
  Flattening{}            -> yellow "flattening"
  Skolemisation{}         -> yellow "skolemisation"
  TrivialInequality{}     -> yellow "trivial inequality"
  EnnfTransformation{}    -> yellow "ennf transformation"
  NnfTransformation{}     -> yellow "nnf transformation"
  Clausification{}        -> yellow "clausification"
  Superposition{}         -> yellow "superposition"
  Resolution{}            -> yellow "resolution"
  Paramodulation{}        -> yellow "paramodulation"
  SubsumptionResolution{} -> yellow "subsumption resolution"
  ForwardDemodulation{}   -> yellow "forward demodulation"
  BackwardDemodulation{}  -> yellow "backward demodulation"
  Unknown{}               -> red "unknown"
  Other name _            -> text (T.unpack name)

instance Pretty l => Pretty (Inference l) where
  pretty (Inference r f) = pretty f <+> brackets (pretty r)

instance Pretty l => Pretty (Sequent l) where
  pretty (Sequent c i) = bold (pretty c <> dot) <+> pretty i

instance (Ord l, Pretty l) => Pretty (Refutation l) where
  pretty r = vsep (pretty <$> sequents r) <> line

-- | List all sequents that lead to the refutation, sorted topologically
-- breadth-first on the graph of inferences.
sequents :: Ord l => Refutation l -> [Sequent Integer]
sequents (Refutation d c) = evalEnumeration $ do
  let ss = breadthFirst d
  let es = labeling ss
  ss' <- foldM (sequentsS es) [] ss
  s <- Sequent <$> next <*> traverse enumerate (liftContradiction c)
  return (reverse (s:ss'))

sequentsS :: Ord l => Map l LogicalExpression ->
             [Sequent Integer] -> Sequent l ->
             Enumeration l [Sequent Integer]
sequentsS es ss s@(Sequent l i) =
  case find trivialClausification (antecedents i) of
    Just a  -> alias l a $> ss
    Nothing -> fmap (:ss) (traverse enumerate s)
  where trivialClausification a = es ! a ~~= consequent i

(~~=) :: LogicalExpression -> LogicalExpression -> Bool
Clause  c ~~= Formula f = triviallyClausified f c
Formula f ~~= Clause  c = triviallyClausified f c
_ ~~= _ = False

triviallyClausified :: Formula -> Clause -> Bool
triviallyClausified f c
  | Just k <- unliftClause f = k ~= c
  | otherwise = False

instance Pretty Proof where
  pretty (Proof p r) = vsep [green meta, pretty r]
    where
      meta = "Found a proof by contradiction using" <+> name <> "."
      name = text (T.unpack $ proverName p)
