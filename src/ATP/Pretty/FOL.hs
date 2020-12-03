{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleInstances #-}

{-|
Module       : ATP.Pretty.FOL
Description  : Pretty-printers for formulas, theorems and proofs.
Copyright    : (c) Evgenii Kotelnikov, 2019-2020
License      : GPL-3
Maintainer   : evgeny.kotelnikov@gmail.com
Stability    : experimental
-}

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
import qualified Data.Text as T (unpack, null)
import System.IO (Handle)

import Text.PrettyPrint.ANSI.Leijen hiding ((<$>))

import ATP.Internal.Enumeration

import ATP.Error
import ATP.FOL


-- * Helper functions

-- | Pretty print to the standard output.
pprint :: Pretty a => a -> IO ()
pprint = putDoc . pretty

-- | Pretty print to an IO handle.
hprint :: Pretty a => Handle -> a -> IO ()
hprint h = hPutDoc h . pretty

prettySequent :: Pretty a => Doc -> a -> Doc
prettySequent h f = bold (h <> dot) <+> pretty f <> line

prettySequents :: Pretty a => Doc -> [a] -> Doc
prettySequents h = hcat . zipWith sequent [1..]
  where sequent i = prettySequent (h <+> integer i)


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

instance Pretty FunctionSymbol where
  pretty (FunctionSymbol s) = text (T.unpack s)

instance Pretty Term where
  pretty = \case
    Variable v    -> prettyVar v
    Function f ts -> prettyApplication (pretty f) (fmap pretty ts)

instance Pretty PredicateSymbol where
  pretty (PredicateSymbol p) = text (T.unpack p)

instance Pretty Literal where
  pretty = \case
    Constant True  -> blue "⟙"
    Constant False -> blue "⟘"
    Predicate p ts -> prettyApplication (pretty p) (fmap pretty ts)
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

  prettyList = prettySequents "Axiom"

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

  prettyList = prettySequents "Axiom"

unitary :: Formula -> Bool
unitary = \case
  Atomic{}     -> True
  Negate{}     -> True
  Connected{}  -> False
  Quantified{} -> True

under :: Connective -> Formula -> Bool
under c = \case
  Connected c' _ _ | c == c' && chainable c -> True
  Quantified{} -> False
  f -> unitary f

chainable :: Connective -> Bool
chainable = \case
  And        -> True
  Or         -> True
  Implies    -> False
  Equivalent -> False
  Xor        -> False

instance Pretty LogicalExpression where
  pretty = \case
    Clause  c -> pretty c
    Formula f -> pretty f


-- * Pretty printer for problems

instance Pretty Clauses where
  pretty (Clauses cs) = prettyList cs

instance Pretty Theorem where
  pretty (Theorem as c) = prettyList as <> prettySequent "Conjecture" c


-- * Pretty printer for proofs

instance Pretty l => Pretty (Rule l) where
  pretty rule = pretty (ruleName rule) <> case nonEmpty (toList rule) of
    Just as -> space <> commaSep (fmap (bold . pretty) as)
    Nothing -> empty

instance Pretty RuleName where
  pretty (RuleName rn) =
    case rn of
      "negated conjecture" -> underline (yellow name)
      "unknown"            -> red name
      "other"              -> name
      _                    -> yellow name
    where
      name = text (T.unpack rn)

instance Pretty l => Pretty (Inference l) where
  pretty (Inference r f) = pretty f <+> brackets (pretty r)

instance Pretty l => Pretty (Sequent l) where
  pretty (Sequent c i) = bold (pretty c <> dot) <+> pretty i

instance (Ord l, Pretty l) => Pretty (Derivation l) where
  pretty d = vsep (pretty <$> derivation d) <> line

instance (Ord l, Pretty l) => Pretty (Refutation l) where
  pretty r = vsep (pretty <$> sequents r) <> line

-- | List all sequents that lead to the refutation, sorted topologically
-- breadth-first on the graph of inferences.
sequents :: Ord l => Refutation l -> [Sequent Integer]
sequents (Refutation d c) = evalEnumeration $ do
  ss <- derivationS d
  s <- Sequent <$> next <*> traverse enumerate (liftContradiction c)
  return (reverse (s:ss))

derivation :: Ord l => Derivation l -> [Sequent Integer]
derivation = evalEnumeration . fmap reverse . derivationS

derivationS :: Ord l => Derivation l -> Enumeration l [Sequent Integer]
derivationS d = foldM (sequentsS es) [] ss
  where
    ss = breadthFirst d
    es = labeling ss

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

instance Pretty Solution where
  pretty = \case
    Saturation d -> vsep [yellow saturated, pretty d]
    Proof r      -> vsep [green proven,     pretty r]
    where
      saturated = "Disproven by constructing the saturated set of clauses."
      proven = "Found a proof by refutation."

instance Pretty Error where
  pretty err = red $ case explanation of
                       Just ex -> vsep [failure, ex]
                       Nothing -> failure
    where
      failure = "Failed to find a solution because" <+> reason <> "."

      reason = case err of
        TimeLimitError    -> "the theorem prover exceeded its time limit"
        MemoryLimitError  -> "the theorem prover exceeded its memory limit"
        ParsingError{}    -> "of the following parsing error"
        ProofError{}      -> "of the following problem with the proof"
        OtherError{}      -> "of the following error"
        ExitCodeError c _ -> "the theorem prover terminated with exit code" <+>
                             bold exitCode <+> "and the following error message"
          where exitCode = text (show c)

      explanation = fmap (text . T.unpack) $ case err of
        TimeLimitError    -> Nothing
        MemoryLimitError  -> Nothing
        ParsingError e    -> Just e
        ProofError   e    -> Just e
        OtherError   e    -> Just e
        ExitCodeError _ e -> if T.null e then Nothing else Just e

instance Pretty a => Pretty (Partial a) where
  pretty = either pretty pretty . liftPartial
