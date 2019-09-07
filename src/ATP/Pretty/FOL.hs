{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}

module ATP.Pretty.FOL (
  Pretty(..),
  putDoc,
  pprint
) where

import Control.Applicative (liftA2)
import Data.Char (digitToInt)
import Data.List (genericIndex)
import Data.List.NonEmpty (NonEmpty(..), nonEmpty)
import Data.Text as T (unpack)

import Text.PrettyPrint.ANSI.Leijen hiding ((<$>))

import ATP.FOL


-- * Helper functions

-- | Pretty print to the standard output.
pprint :: Pretty a => a -> IO ()
pprint = putDoc . pretty


-- * Pretty printer for formulas

prettyVar :: Var -> Doc
prettyVar v = cyan . text $ genericIndex variables (abs v)
  where
    variables :: [String]
    variables = liftA2 prime [0..] ["v", "x", "y", "z", "t"]

    prime :: Integer -> String -> String
    prime n w = letter <> index
      where
        letter = if v >= 0 then w  else w <> "′"
        index  = if n == 0 then "" else fmap ("₀₁₂₃₄₅₆₇₈₉" !!) (digits n)
        digits = fmap digitToInt . show

prettySymbol :: Symbol -> Doc
prettySymbol = text . unpack

prettyFunction, prettyPredicate :: Symbol -> Doc
prettyFunction  = prettySymbol
prettyPredicate = prettySymbol

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
    Constant True  -> red "⟙"
    Constant False -> red "⟘"
    Predicate p ts -> prettyApplication (prettyPredicate p) (fmap pretty ts)
    Equality a b   -> pretty a <+> "=" <+> pretty b

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
    Connected f c g  -> prettyParens (under c) f <+> pretty c
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
  Connected _ c' _ | c == c' && isAssociative c -> True
  Quantified{} -> False
  f -> unitary f


-- * Pretty printer for theorems

instance Pretty Theorem where
  pretty = \case
    Theorem as c -> vsep (zipWith prettyAxiom [1..] as ++ [prettyConjecture]) <> line
      where
        prettyAxiom i a = bold ("Axiom" <+> integer i <> dot) <+> pretty a
        prettyConjecture = bold ("Conjecture" <> dot) <+> pretty c
