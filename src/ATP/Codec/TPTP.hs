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
  encodeTheorem,
  decodeRefutation
) where

import Control.Applicative (liftA2)
import Control.Monad (when)
import Control.Monad.State (State, evalState, get, modify)
import Data.List (genericIndex)
import Data.Map (Map)
import qualified Data.Map as M (empty, lookup, insert, member)
#if !MIN_VERSION_base(4, 11, 0)
import Data.Semigroup (Semigroup(..))
#endif
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.TPTP as TPTP

import ATP.FOL
import ATP.Proof (Inference(..), Derivation(..), Refutation(..))


-- * Helpers

type Enumeration a = State (Integer, Map a Integer)

evalEnumeration :: Enumeration a e -> e
evalEnumeration = flip evalState (1, M.empty)

register :: Ord a => a -> Enumeration a ()
register a = modify $ \(i, m) -> (i + 1, M.insert a i m)


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
decodeVar v = do
  (i, s) <- get
  case M.lookup v s of
    Just w  -> return w
    Nothing -> register v >> return i

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
  TPTP.Conjunction -> \f g -> Connected f And g
  TPTP.Disjunction -> \f g -> Connected f Or g
  TPTP.Implication -> \f g -> Connected f Implies g
  TPTP.Equivalence -> \f g -> Connected f Equivalent g
  TPTP.ExclusiveOr -> \f g -> Connected f Xor g
  TPTP.NegatedConjunction  -> \f g -> Negate (Connected f And g)
  TPTP.NegatedDisjunction  -> \f g -> Negate (Connected f Or g)
  TPTP.ReversedImplication -> \f g -> Connected g Implies f

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
decodeFormula = evalEnumeration . decodeFormulaS

decodeFormulaS :: TPTP.UnsortedFirstOrder -> Substitutions Formula
decodeFormulaS = \case
  TPTP.Atomic l          -> decodeLiteral l
  TPTP.Negated f         -> Negate <$> decodeFormulaS f
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
decodeClause = evalEnumeration . decodeClauseS

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

-- | Decode a proof by refutation from a TSTP output.
decodeRefutation :: TPTP.TSTP -> Refutation Integer
decodeRefutation (TPTP.TSTP szs units)
  | TPTP.SZS (Just _status) (Just _dataform) <- szs =
    case reverse (decodeDerivations units) of
      Derivation inference Falsum : derivations -> Refutation inference derivations
      _:_ -> error "decodeRefutation: malformed input: refutation not found"
      []  -> error "decodeRefutation: malformed input: empty proof"
  | otherwise = error "decodeRefutation: malformed input: missing SZS ontologies"

decodeDerivations :: [TPTP.Unit] -> [Derivation Integer]
decodeDerivations = evalEnumeration . mapM decodeDerivationS

decodeDerivationS :: TPTP.Unit -> Enumeration TPTP.UnitName (Derivation Integer)
decodeDerivationS = \case
  TPTP.Unit name (TPTP.Formula role formula) (Just (source, _)) -> do
    (label, relabeling) <- get
    when (M.member name relabeling)
         (error "decodeDerivationS: malformed input: non-unique units")
    register name
    let antecedents = fmap (decodeUnitName relabeling) (collectParents source)
    let inference = decodeInference source role antecedents label
    return $ Derivation inference (decode formula)
  _ -> error "decodeDerivationS: malformed input: expected unit"

collectParents :: TPTP.Source -> [TPTP.UnitName]
collectParents = \case
  TPTP.File{}        -> []
  TPTP.Theory{}      -> []
  TPTP.Creator{}     -> []
  TPTP.Introduced{}  -> []
  TPTP.Inference _ _ ps -> concatMap (\(TPTP.Parent p _) -> collectParents p) ps
  TPTP.UnitSource p  -> [p]
  TPTP.UnknownSource -> []

decodeUnitName :: Map TPTP.UnitName l -> TPTP.UnitName -> l
decodeUnitName relabeling name
  | Just label <- M.lookup name relabeling = label
  | otherwise = error "decodeUnitName: malformed input: unrecognized unit"

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
    ("subsumption_resolution",  [f, g]) -> SubsumptionResolution f g
    ("forward_demodulation",    [f, g]) -> ForwardDemodulation   f g
    ("backward_demodulation",   [f, g]) -> BackwardDemodulation  f g
    _ -> Other rule antecedents
