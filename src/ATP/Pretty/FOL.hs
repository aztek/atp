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
import Data.Char (digitToInt)
import Data.List (genericIndex)
import Data.List.NonEmpty (NonEmpty(..), nonEmpty, toList)
import Data.Text as T (unpack)
import System.IO (Handle)

import Text.PrettyPrint.ANSI.Leijen hiding ((<$>))

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


-- * Pretty printer for theorems

instance Pretty Theorem where
  pretty = \case
    Theorem as c -> vsep (zipWith axiom [1..] as ++ [conclusion c]) <> line
      where
        axiom i = sequent ("Axiom" <+> integer i)
        conclusion = sequent "Conjecture"
        sequent h f = bold (h <> dot) <+> pretty f


-- * Pretty printer for proofs

instance Pretty l => Pretty (Inference l) where
  pretty i
    | Just as <- nonEmpty (antecedents i) =
        prettyRule i <+> commaSep (fmap (bold . pretty) as)
    | otherwise = prettyRule i

prettyRule :: Inference l -> Doc
prettyRule = \case
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
  SubsumptionResolution{} -> yellow "subsumption resolution"
  ForwardDemodulation{}   -> yellow "forward demodulation"
  BackwardDemodulation{}  -> yellow "backward demodulation"
  Unknown{}               -> red "unknown"
  Other name _ _          -> text (T.unpack name)

instance Pretty l => Pretty (Derivation l) where
  pretty (Derivation i f) =  bold (pretty (consequent i) <> dot) <+> pretty f
                         <+> brackets (pretty i)

instance Pretty l => Pretty (Refutation l) where
  pretty p = vsep (toList . fmap pretty $ derivations p) <> line

instance Pretty Proof where
  pretty (Proof p r) = vsep [green meta, pretty r]
    where
      meta = "Found a proof by contradiction using" <+> name <> "."
      name = text (T.unpack $ proverName p)
