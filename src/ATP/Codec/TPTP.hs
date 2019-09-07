{-# LANGUAGE CPP #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}

{-|
Module       : ATP.Codec.TPTP
Description  : Coding and decoding of unsorted first-order logic in TPTP.
Copyright    : (c) Evgenii Kotelnikov, 2019
License      : GPL-3
Maintainer   : evgeny.kotelnikov@gmail.com
Stability    : experimental
-}

module ATP.Codec.TPTP (
  encode,
  decode,
  encodeFormula,
  decodeFormula,
  decodeClause,
  encodeTheorem
) where

import Control.Monad.State (State, evalState, get, modify)
import Data.List (genericIndex)
import Data.Map (Map)
import qualified Data.Map as M (empty, elems, lookup, insert)
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.TPTP as TPTP

import ATP.FOL


-- | Encode a variable in TPTP.
--
-- >>> encodeVar 0
-- Var "X"
--
-- >>> encodeVar 1
-- Var "Y"
--
-- >>> encodeVar 7
-- Var "X1"
--
-- >>> encodeVar (-1)
-- Var "YY"
--
-- >>> encodeVar (-7)
-- Var "XX1"
--
-- 'encodeVar' is injective.
--
-- prop> (v == v') == (encodeVar v == encodeVar v')
--
encodeVar :: Var -> TPTP.Var
encodeVar v = TPTP.Var $ genericIndex variables (abs v)
  where
    variables :: [Text]
    variables = liftA2 prime [0..] ["X", "Y", "Z", "P", "Q", "R", "T"]

    prime :: Integer -> Text -> Text
    prime n w = letter <> index
      where
        letter = if v >= 0 then w else w <> w
        index  = if n == 0 then T.empty else T.pack (show n)

type Substitutions = State (Map TPTP.Var Var)

-- | Decode a variable from TPTP.
decodeVar :: TPTP.Var -> Substitutions Var
decodeVar v = do
  substitutions <- get
  case M.lookup v substitutions of
    Just w  -> return w
    Nothing -> modify (M.insert v fresh) >> return fresh
      where fresh = 1 + if null elems then 0 else maximum elems
            elems = M.elems substitutions

-- | Encode a function symbol in TPTP.
encodeFunction :: Symbol -> TPTP.Name TPTP.Function
encodeFunction = TPTP.Defined . TPTP.Atom

-- | Decode a function symbol from TPTP.
decodeFunction :: TPTP.Name s -> Symbol
decodeFunction = \case
  TPTP.Defined (TPTP.Atom s) -> s
  TPTP.Reserved{} ->
    error "decodeFunction: reserved functions are not supported"

-- | Encode a predicate symbol in TPTP.
encodePredicate :: Symbol -> TPTP.Name TPTP.Predicate
encodePredicate = TPTP.Defined . TPTP.Atom

-- | Encode a term in TPTP.
encodeTerm :: Term -> TPTP.Term
encodeTerm = \case
  Variable v    -> TPTP.Variable (encodeVar v)
  Function f ts -> TPTP.Function (encodeFunction f) (fmap encodeTerm ts)

-- | Decode a term from TPTP.
decodeTermS :: TPTP.Term -> Substitutions Term
decodeTermS = \case
  TPTP.Function f ts  -> function (decodeFunction f) <$> traverse decodeTermS ts
  TPTP.Variable v     -> Variable <$> decodeVar v
  TPTP.Number{}       -> error "decodeTermS: numbers are not supported"
  TPTP.DistinctTerm{} -> error "decodeTermS: distinct objects are not supported"

-- | Encode a literal in TPTP.
encodeLiteral :: Literal -> TPTP.Literal
encodeLiteral = \case
  Predicate p ts -> TPTP.Predicate (encodePredicate p) (fmap encodeTerm ts)
  Equality a b   -> TPTP.Equality (encodeTerm a) TPTP.Positive (encodeTerm b)
  Constant b     -> TPTP.Predicate (TPTP.Reserved (TPTP.Standard p)) []
    where p = if b then TPTP.Tautology else TPTP.Falsum

-- | Decode a literal from TPTP.
decodeLiteral :: TPTP.Literal -> Substitutions Formula
decodeLiteral = \case
  TPTP.Predicate p ts -> decodePredicate p <$> traverse decodeTermS ts
  TPTP.Equality a s b -> decodeSign s <$> decodeTermS a <*> decodeTermS b

decodePredicate :: TPTP.Name TPTP.Predicate -> [Term] -> Formula
decodePredicate = \case
  TPTP.Defined  (TPTP.Atom p)                  -> predicate p
  TPTP.Reserved (TPTP.Standard TPTP.Tautology) -> const tautology
  TPTP.Reserved (TPTP.Standard TPTP.Falsum)    -> const falsum
  TPTP.Reserved TPTP.Standard{} ->
    error "decodePredicate: unsupported standard reserved predicate"
  TPTP.Reserved TPTP.Extended{} ->
    error "decodePredicate: extended reserved predicates are not supported"

decodeSign :: TPTP.Sign -> Term -> Term -> Formula
decodeSign = \case
  TPTP.Positive -> (===)
  TPTP.Negative -> (=/=)

-- | Encode a logical connective in TPTP.
encodeConnective :: Connective -> TPTP.Connective
encodeConnective = \case
  And        -> TPTP.Conjunction
  Or         -> TPTP.Disjunction
  Implies    -> TPTP.Implication
  Equivalent -> TPTP.Equivalence
  Xor        -> TPTP.ExclusiveOr

decodeConnected :: TPTP.Connective -> Formula -> Formula -> Formula
decodeConnected = \case
  TPTP.Conjunction -> (/\)
  TPTP.Disjunction -> (\/)
  TPTP.Implication -> (==>)
  TPTP.Equivalence -> (<=>)
  TPTP.ExclusiveOr -> (<~>)
  TPTP.NegatedConjunction  -> \f g -> neg (f /\ g)
  TPTP.NegatedDisjunction  -> \f g -> neg (f \/ g)
  TPTP.ReversedImplication -> flip (==>)

-- | Encode a quantifier in TPTP.
encodeQuantifier :: Quantifier -> TPTP.Quantifier
encodeQuantifier = \case
  Forall -> TPTP.Forall
  Exists -> TPTP.Exists

-- | Decode a quantifier from TPTP.
decodeQuantifier :: TPTP.Quantifier -> Quantifier
decodeQuantifier = \case
  TPTP.Forall -> Forall
  TPTP.Exists -> Exists

-- | Encode a formula in unsorted first-order logic in TPTP.
encodeFormula :: Formula -> TPTP.UnsortedFirstOrder
encodeFormula = \case
  Atomic l         -> TPTP.Atomic (encodeLiteral l)
  Negate f         -> TPTP.Negated (encodeFormula f)
  Connected f c g  -> TPTP.Connected (encodeFormula f) (encodeConnective c) (encodeFormula g)
  Quantified q v f -> TPTP.quantified (encodeQuantifier q) [(encodeVar v, TPTP.Unsorted ())] (encodeFormula f)

-- | Decode a formula in unsorted first-order logic from TPTP.
decodeFormula :: TPTP.UnsortedFirstOrder -> Formula
decodeFormula = flip evalState M.empty . decodeFormulaS

decodeFormulaS :: TPTP.UnsortedFirstOrder -> Substitutions Formula
decodeFormulaS = \case
  TPTP.Atomic l          -> decodeLiteral l
  TPTP.Negated f         -> neg <$> decodeFormulaS f
  TPTP.Connected f c g   -> decodeConnected c
                        <$> decodeFormulaS f <*> decodeFormulaS g
  TPTP.Quantified q vs f -> foldr (curry $ quantified (decodeQuantifier q))
                        <$> decodeFormulaS f <*> traverse (decodeVar . fst) vs

-- | Encode a formula in unsorted first-order logic in TPTP.
encode :: Formula -> TPTP.Formula
encode = TPTP.FOF . encodeFormula

-- | Decode a formula in unsorted first-order logic from TPTP.
decode :: TPTP.Formula -> Formula
decode = \case
  TPTP.FOF f  -> decodeFormula f
  TPTP.CNF c  -> decodeClause  c
  TPTP.TFF0{} -> error "decode: formulas in TFF0 are not supported"
  TPTP.TFF1{} -> error "decode: formulas in TFF1 are not supported"

-- | Decode a clause in unsorted first-order logic from TPTP.
decodeClause :: TPTP.Clause -> Formula
decodeClause = flip evalState M.empty . decodeClauseS

decodeClauseS :: TPTP.Clause -> Substitutions Formula
decodeClauseS (TPTP.Clause ls) = disjunction <$> traverse decodeSignedLiteral ls

decodeSignedLiteral :: (TPTP.Sign, TPTP.Literal) -> Substitutions Formula
decodeSignedLiteral = uncurry $ \case
  TPTP.Positive -> decodeLiteral
  TPTP.Negative -> fmap neg . decodeLiteral

-- | Encode a theorem in unsorted first-order logic in TPTP.
encodeTheorem :: Theorem -> TPTP.TPTP
encodeTheorem (Theorem as c) = TPTP.TPTP units
  where
    units = unit TPTP.Conjecture 0 c : zipWith (unit TPTP.Axiom) [1..] as
    unit r n f = TPTP.Unit (Right n) (formula r f) Nothing
    formula r f = TPTP.Formula (TPTP.Standard r) (encode f)
