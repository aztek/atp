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
  encodeClause,
  decodeClause,
  encodeTheorem,
  decodeRefutation
) where

import Control.Applicative (liftA2)
import Control.Monad (foldM)
import Control.Monad.State (State, evalState, gets, modify)
import Data.List (genericIndex, find)
import qualified Data.List.NonEmpty as NE (toList)
import Data.Map (Map, (!))
import qualified Data.Map as M (empty, lookup, insert)
#if !MIN_VERSION_base(4, 11, 0)
import Data.Semigroup (Semigroup(..))
#endif
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.TPTP as TPTP

import ATP.FOL hiding (antecedents, consequent, derivations)


-- * Helpers

type Enumeration a = State (Integer, Map a Integer)

evalEnumeration :: Enumeration a e -> e
evalEnumeration = flip evalState (1, M.empty)

fresh :: Enumeration a Integer
fresh = do
  i <- gets fst
  modify $ \(j, m) -> (j + 1, m)
  return i

register :: Ord a => a -> Integer -> Enumeration a ()
register a i = modify $ fmap (M.insert a i)

alias :: Ord a => a -> a -> Enumeration a ()
alias original synonym = do
  v <- gets (M.lookup original . snd)
  i <- case v of
    Just i -> return i
    Nothing -> do
      i <- fresh
      register original i
      return i
  register synonym i


-- * Coding and decoding

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

type Substitutions = Enumeration TPTP.Var

-- | Decode a variable from TPTP.
decodeVar :: TPTP.Var -> Substitutions Var
decodeVar v = gets (M.lookup v . snd) >>= \case
  Just w -> return w
  Nothing -> do
    i <- fresh
    register v i
    return i

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
  TPTP.Function f ts  -> Function (decodeFunction f) <$> traverse decodeTermS ts
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
decodeLiteral :: TPTP.Literal -> Substitutions (Signed Literal)
decodeLiteral = \case
  TPTP.Predicate p ts -> Signed Positive . decodePredicate p <$> traverse decodeTermS ts
  TPTP.Equality a s b -> decodeEquality s <$> decodeTermS a <*> decodeTermS b

decodePredicate :: TPTP.Name TPTP.Predicate -> [Term] -> Literal
decodePredicate = \case
  TPTP.Defined  (TPTP.Atom p)                  -> Predicate p
  TPTP.Reserved (TPTP.Standard TPTP.Tautology) -> const (Constant True)
  TPTP.Reserved (TPTP.Standard TPTP.Falsum)    -> const (Constant False)
  TPTP.Reserved TPTP.Standard{} ->
    error "decodePredicate: unsupported standard reserved predicate"
  TPTP.Reserved TPTP.Extended{} ->
    error "decodePredicate: extended reserved predicates are not supported"

decodeEquality :: TPTP.Sign -> Term -> Term -> Signed Literal
decodeEquality s a b = Signed (decodeSign s) (Equality a b)

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
  TPTP.Conjunction -> Connected And
  TPTP.Disjunction -> Connected Or
  TPTP.Implication -> Connected Implies
  TPTP.Equivalence -> Connected Equivalent
  TPTP.ExclusiveOr -> Connected Xor
  TPTP.NegatedConjunction  -> Negate .: Connected And
  TPTP.NegatedDisjunction  -> Negate .: Connected Or
  TPTP.ReversedImplication -> flip (Connected Implies)
  where
    (.:) :: (c -> d) -> (a -> b -> c) -> a -> b -> d
    (.:) = (.) . (.)

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
  Connected  c f g -> TPTP.Connected (encodeFormula f) (encodeConnective c) (encodeFormula g)
  Quantified q v f -> TPTP.quantified (encodeQuantifier q) [(encodeVar v, TPTP.Unsorted ())] (encodeFormula f)

-- | Decode a formula in unsorted first-order logic from TPTP.
decodeFormula :: TPTP.UnsortedFirstOrder -> Formula
decodeFormula = evalEnumeration . decodeFormulaS

decodeFormulaS :: TPTP.UnsortedFirstOrder -> Substitutions Formula
decodeFormulaS = \case
  TPTP.Atomic l          -> liftSignedLiteral <$> decodeLiteral l
  TPTP.Negated f         -> Negate <$> decodeFormulaS f
  TPTP.Connected f c g   -> decodeConnected c
                        <$> decodeFormulaS f <*> decodeFormulaS g
  TPTP.Quantified q vs f -> foldr (curry $ quantified (decodeQuantifier q))
                        <$> decodeFormulaS f <*> traverse (decodeVar . fst) vs

-- | Encode a formula in unsorted first-order logic in TPTP.
encode :: LogicalExpression -> TPTP.Formula
encode = \case
  Clause  c -> TPTP.CNF (encodeClause  c)
  Formula f -> TPTP.FOF (encodeFormula f)

-- | Decode a formula in unsorted first-order logic from TPTP.
decode :: TPTP.Formula -> LogicalExpression
decode = \case
  TPTP.FOF f  -> Formula (decodeFormula f)
  TPTP.CNF c  -> Clause  (decodeClause  c)
  TPTP.TFF0{} -> error "decode: formulas in TFF0 are not supported"
  TPTP.TFF1{} -> error "decode: formulas in TFF1 are not supported"

-- | Encode a clause in unsorted first-order logic in TPTP.
encodeClause :: Clause -> TPTP.Clause
encodeClause (Literals ls) = TPTP.clause (fmap encodeSignedLiteral ls)

-- | Decode a clause in unsorted first-order logic from TPTP.
decodeClause :: TPTP.Clause -> Clause
decodeClause = evalEnumeration . decodeClauseS

decodeClauseS :: TPTP.Clause -> Substitutions Clause
decodeClauseS (TPTP.Clause ls) = Literals <$> traverse decodeSignedLiteralS (NE.toList ls)

encodeSign :: Sign -> TPTP.Sign
encodeSign = \case
  Positive -> TPTP.Positive
  Negative -> TPTP.Negative

decodeSign :: TPTP.Sign -> Sign
decodeSign = \case
  TPTP.Positive -> Positive
  TPTP.Negative -> Negative

encodeSignedLiteral :: Signed Literal -> (TPTP.Sign, TPTP.Literal)
encodeSignedLiteral (Signed s l) = (encodeSign s, encodeLiteral l)

decodeSignedLiteralS :: (TPTP.Sign, TPTP.Literal) -> Substitutions (Signed Literal)
decodeSignedLiteralS (s, l) = sign (decodeSign s) <$> decodeLiteral l

-- | Encode a theorem in unsorted first-order logic in TPTP.
encodeTheorem :: Theorem -> TPTP.TPTP
encodeTheorem (Theorem as c) = TPTP.TPTP units
  where
    units = unit TPTP.Conjecture 0 c : zipWith (unit TPTP.Axiom) [1..] as
    unit r n f = TPTP.Unit (Right n) (formula r f) Nothing
    formula r f = TPTP.Formula (TPTP.Standard r) (encode $ Formula f)

-- | Decode a proof by refutation from a TSTP output.
decodeRefutation :: TPTP.TSTP -> Refutation Integer
decodeRefutation (TPTP.TSTP szs units)
  | TPTP.SZS (Just _status) (Just _dataform) <- szs =
    case decodeDerivations units of
      Derivation inference conclusion : derivations
        | isContradiction conclusion -> Refutation inference derivations
      _:_ -> error "decodeRefutation: malformed input: refutation not found"
      []  -> error "decodeRefutation: malformed input: empty proof"
  | otherwise = error "decodeRefutation: malformed input: missing SZS ontologies"

isContradiction :: LogicalExpression -> Bool
isContradiction = \case
  Clause c | Falsum <- liftClause c -> True
  Formula Falsum -> True
  _ -> False

decodeDerivations :: [TPTP.Unit] -> [Derivation Integer]
decodeDerivations units = evalEnumeration (foldM (decodeDerivationS labels) [] decodedUnits)
  where
    labels = labeling decodedUnits
    decodedUnits = fmap decodeDerivation units

decodeDerivationS :: Map TPTP.UnitName LogicalExpression ->
                     [Derivation Integer] -> Derivation TPTP.UnitName ->
                     Enumeration TPTP.UnitName [Derivation Integer]
decodeDerivationS labels derivations derivation@(Derivation inference formula) =
  case find (\index -> labels ! index ~= formula) antecedents of
    Just index -> do
      alias index consequent
      return derivations
    Nothing -> do
      derivation' <- traverse decodeUnitNameS derivation
      return (derivation':derivations)
  where
    (antecedents, consequent) = sequents inference

decodeDerivation :: TPTP.Unit -> Derivation TPTP.UnitName
decodeDerivation = \case
  TPTP.Unit name (TPTP.Formula role formula) (Just (source, _)) -> derivation
    where
      derivation = Derivation inference (decode formula)
      inference  = decodeInference source role (collectParents source) name
  _ -> error "decodeDerivation: malformed input: expected unit"

collectParents :: TPTP.Source -> [TPTP.UnitName]
collectParents = \case
  TPTP.File{}        -> []
  TPTP.Theory{}      -> []
  TPTP.Creator{}     -> []
  TPTP.Introduced{}  -> []
  TPTP.Inference _ _ ps -> concatMap (\(TPTP.Parent p _) -> collectParents p) ps
  TPTP.UnitSource p  -> [p]
  TPTP.UnknownSource -> []

decodeUnitNameS :: TPTP.UnitName -> Enumeration TPTP.UnitName Integer
decodeUnitNameS name = do
  relabeling <- gets snd
  case M.lookup name relabeling of
    Just label -> return label
    Nothing -> do
      label <- fresh
      register name label
      return label

decodeInference :: TPTP.Source -> TPTP.Reserved TPTP.Role -> [f] -> f -> Inference f
decodeInference source role antecedents = case source of
  TPTP.Theory{}      -> error "decodeInference: unsupported unit source"
  TPTP.Creator{}     -> error "decodeInference: unsupported unit source"
  TPTP.UnitSource{}  -> error "decodeInference: unsupported unit source"
  TPTP.Introduced{}  -> Axiom
  TPTP.UnknownSource -> Unknown antecedents
  TPTP.File{} -> case (role, antecedents) of
    (TPTP.Standard TPTP.Axiom,      []) -> Axiom
    (TPTP.Standard TPTP.Conjecture, []) -> Conjecture
    _ -> error $ "decodeInference: unrecognized unit role " ++ show role
  TPTP.Inference (TPTP.Atom rule) _ _ -> case (rule, antecedents) of
    ("negated_conjecture",         [f]) -> NegatedConjecture       f
    ("assume_negation",            [f]) -> NegatedConjecture       f
    ("flattening",                 [f]) -> Flattening              f
    ("skolemisation",              [f]) -> Skolemisation           f
    ("skolemize",                  [f]) -> Skolemisation           f
    ("ennf_transformation",        [f]) -> EnnfTransformation      f
    ("nnf_transformation",         [f]) -> NnfTransformation       f
    ("cnf_transformation",         [f]) -> Clausification          f
    ("trivial_inequality_removal", [f]) -> TrivialInequality       f
    ("superposition",           [f, g]) -> Superposition         f g
    ("resolution",              [f, g]) -> Resolution            f g
    ("pm",                      [f, g]) -> Paramodulation        f g
    ("subsumption_resolution",  [f, g]) -> SubsumptionResolution f g
    ("forward_demodulation",    [f, g]) -> ForwardDemodulation   f g
    ("backward_demodulation",   [f, g]) -> BackwardDemodulation  f g
    _ -> Other rule antecedents
