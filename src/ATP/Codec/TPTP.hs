{-# LANGUAGE CPP #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}

{-|
Module       : ATP.Codec.TPTP
Description  : Encoding of unsorted first-order logic in TPTP.
Copyright    : (c) Evgenii Kotelnikov, 2019
License      : GPL-3
Maintainer   : evgeny.kotelnikov@gmail.com
Stability    : experimental
-}

module ATP.Codec.TPTP (
  encodeFormula,
  encodeTheorem
) where

import Data.List (genericIndex)
#if !MIN_VERSION_base(4, 11, 0)
import Data.Semigroup ((<>))
#endif
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.TPTP as TPTP

import ATP.FOL

-- | Encode a variable in TPTP.
encodeVar :: Var -> TPTP.Var
encodeVar = TPTP.Var . genericIndex variables
  where
    variables :: [Text]
    variables = concatMap (\n -> fmap (prime n) letters) [0..]

    letters :: [Text]
    letters = ["X", "Y", "Z", "P", "Q", "R", "T"]

    prime :: Integer -> Text -> Text
    prime 0 v = v
    prime n v = v <> T.pack (show n)

-- | Encode a function symbol in TPTP.
encodeFunction :: Symbol -> TPTP.Name TPTP.Function
encodeFunction = TPTP.Defined . TPTP.Atom

-- | Encode a predicate symbol in TPTP.
encodePredicate :: Symbol -> TPTP.Name TPTP.Predicate
encodePredicate = TPTP.Defined . TPTP.Atom

-- | Encode a term in TPTP.
encodeTerm :: Term -> TPTP.Term
encodeTerm = \case
  Variable v    -> TPTP.Variable (encodeVar v)
  Function f ts -> TPTP.Function (encodeFunction f) (fmap encodeTerm ts)

-- | Encode a literal in TPTP.
encodeLiteral :: Literal -> TPTP.Literal
encodeLiteral = \case
  Predicate p ts -> TPTP.Predicate (encodePredicate p) (fmap encodeTerm ts)
  Equality a b   -> TPTP.Equality (encodeTerm a) TPTP.Positive (encodeTerm b)
  Constant b     -> TPTP.Predicate (TPTP.Reserved (TPTP.Standard p)) []
    where p = if b then TPTP.Tautology else TPTP.Falsum

-- | Encode a logical connective in TPTP.
encodeConnective :: Connective -> TPTP.Connective
encodeConnective = \case
  And        -> TPTP.Conjunction
  Or         -> TPTP.Disjunction
  Implies    -> TPTP.Implication
  Equivalent -> TPTP.Equivalence
  Xor        -> TPTP.ExclusiveOr

-- | Encode a quantifier in TPTP.
encodeQuantifier :: Quantifier -> TPTP.Quantifier
encodeQuantifier = \case
  Forall -> TPTP.Forall
  Exists -> TPTP.Exists

-- | Encode a formula in unsorted first-order logic in TPTP.
encodeFormula :: Formula -> TPTP.UnsortedFirstOrder
encodeFormula = \case
  Atomic l         -> TPTP.Atomic (encodeLiteral l)
  Negate f         -> TPTP.Negated (encodeFormula f)
  Connected f c g  -> TPTP.Connected (encodeFormula f) (encodeConnective c) (encodeFormula g)
  Quantified q v f -> TPTP.quantified (encodeQuantifier q) [(encodeVar v, TPTP.Unsorted ())] (encodeFormula f)

-- | Encode a theorem in unsorted first-order logic in TPTP.
encodeTheorem :: Theorem -> TPTP.TPTP
encodeTheorem (Theorem as c) = TPTP.TPTP units
  where
    units = unit TPTP.Conjecture 0 c
          : fmap (uncurry $ unit TPTP.Axiom) (zip [1..] as)
    unit r n f = TPTP.Unit (Right n) (formula r f) Nothing
    formula r f = TPTP.Formula (TPTP.Standard r) (fof f)
    fof = TPTP.FOF . encodeFormula
