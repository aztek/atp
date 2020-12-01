{-# LANGUAGE CPP #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiWayIf #-}
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
  encodeClauseSet,
  decodeSolution
) where

import Control.Applicative (liftA2)
import Control.Monad (foldM)
import Control.Monad.Trans (lift)
import Data.Functor (($>))
import Data.List (genericIndex, find)
import qualified Data.List.NonEmpty as NE (toList)
import Data.Map (Map, (!))
#if !MIN_VERSION_base(4, 11, 0)
import Data.Semigroup (Semigroup(..))
#endif
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.TPTP as TPTP

import ATP.Internal.Enumeration
import ATP.Error
import ATP.FOL


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
-- @encodeVar@ is injective.
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

type Substitutions = EnumerationT TPTP.Var Partial

-- | Encode a function symbol in TPTP.
encodeFunction :: FunctionSymbol -> TPTP.Name TPTP.Function
encodeFunction (FunctionSymbol s) = TPTP.Defined (TPTP.Atom s)

-- | Decode a function symbol from TPTP.
decodeFunction :: TPTP.Name s -> Partial FunctionSymbol
decodeFunction = \case
  TPTP.Defined (TPTP.Atom s) -> return (FunctionSymbol s)
  TPTP.Reserved{} -> parsingError "reserved functions are not supported"

-- | Encode a predicate symbol in TPTP.
encodePredicate :: PredicateSymbol -> TPTP.Name TPTP.Predicate
encodePredicate (PredicateSymbol p) = TPTP.Defined (TPTP.Atom p)

-- | Encode a term in TPTP.
encodeTerm :: Term -> TPTP.Term
encodeTerm = \case
  Variable v    -> TPTP.Variable (encodeVar v)
  Function f ts -> TPTP.Function (encodeFunction f) (fmap encodeTerm ts)

-- | Decode a term from TPTP.
decodeTermS :: TPTP.Term -> Substitutions Term
decodeTermS = \case
  TPTP.Function f ts  -> Function <$> lift (decodeFunction f) <*> traverse decodeTermS ts
  TPTP.Variable v     -> Variable <$> enumerate v
  TPTP.Number{}       -> lift $ parsingError "numbers are not supported"
  TPTP.DistinctTerm{} -> lift $ parsingError "distinct objects are not supported"

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
  TPTP.Predicate p ts -> do
    p' <- lift (decodePredicate p)
    ts' <- traverse decodeTermS ts
    return $ Signed Positive (p' ts')
  TPTP.Equality a s b -> decodeEquality s <$> decodeTermS a <*> decodeTermS b

decodePredicate :: TPTP.Name TPTP.Predicate -> Partial ([Term] -> Literal)
decodePredicate = \case
  TPTP.Defined  (TPTP.Atom p)                  -> return $ Predicate (PredicateSymbol p)
  TPTP.Reserved (TPTP.Standard TPTP.Tautology) -> return $ const (Constant True)
  TPTP.Reserved (TPTP.Standard TPTP.Falsum)    -> return $ const (Constant False)
  TPTP.Reserved (TPTP.Standard p) ->
    parsingError $ "unsupported standard reserved predicate " <> show p
  TPTP.Reserved TPTP.Extended{} ->
    parsingError "extended reserved predicates are not supported"

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
decodeFormula :: TPTP.UnsortedFirstOrder -> Partial Formula
decodeFormula = evalEnumerationT . decodeFormulaS

decodeFormulaS :: TPTP.UnsortedFirstOrder -> Substitutions Formula
decodeFormulaS = \case
  TPTP.Atomic l          -> liftSignedLiteral <$> decodeLiteral l
  TPTP.Negated f         -> Negate <$> decodeFormulaS f
  TPTP.Connected f c g   -> decodeConnected c
                        <$> decodeFormulaS f <*> decodeFormulaS g
  TPTP.Quantified q vs f -> foldr (curry $ quantified (decodeQuantifier q))
                        <$> decodeFormulaS f <*> traverse (enumerate . fst) vs

-- | Encode a formula in unsorted first-order logic in TPTP.
encode :: LogicalExpression -> TPTP.Formula
encode = \case
  Clause  c -> TPTP.CNF (encodeClause  c)
  Formula f -> TPTP.FOF (encodeFormula f)

-- | Decode a formula in unsorted first-order logic from TPTP.
decode :: TPTP.Formula -> Partial LogicalExpression
decode = \case
  TPTP.FOF f  -> Formula <$> decodeFormula f
  TPTP.CNF c  -> Clause  <$> decodeClause  c
  TPTP.TFF0{} -> parsingError "formulas in TFF0 are not supported"
  TPTP.TFF1{} -> parsingError "formulas in TFF1 are not supported"

-- | Encode a clause in unsorted first-order logic in TPTP.
encodeClause :: Clause -> TPTP.Clause
encodeClause = TPTP.clause . fmap encodeSignedLiteral . unClause

-- | Decode a clause in unsorted first-order logic from TPTP.
decodeClause :: TPTP.Clause -> Partial Clause
decodeClause = evalEnumerationT . decodeClauseS

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

-- | Encode a set of first-order clauses in TPTP.
encodeClauseSet :: ClauseSet -> TPTP.TPTP
encodeClauseSet (ClauseSet cs) = TPTP.TPTP units
  where
    units = zipWith unit [1..] cs
    unit n f = TPTP.Unit (Right n) (clauze f) Nothing
    clauze = TPTP.Formula (TPTP.Standard TPTP.Axiom) . encode . Clause

-- | Encode a theorem in unsorted first-order logic in TPTP.
encodeTheorem :: Theorem -> TPTP.TPTP
encodeTheorem (Theorem as c) = TPTP.TPTP units
  where
    units = unit TPTP.Conjecture 0 c : zipWith (unit TPTP.Axiom) [1..] as
    unit r n f = TPTP.Unit (Right n) (formula r f) Nothing
    formula r f = TPTP.Formula (TPTP.Standard r) (encode $ Formula f)

-- | Decode a solution from a TSTP output.
decodeSolution :: TPTP.TSTP -> Partial Solution
decodeSolution (TPTP.TSTP szs units)
  | TPTP.SZS (Just (Right status)) _dataform <- szs = if
    | isProof status -> Proof <$> decodeRefutation units
    | isSaturation status -> Saturation <$> decodeDerivation units
    | otherwise -> parsingError $ "unsupported SZS " <> show status
  | otherwise = proofError "malformed input: missing SZS ontologies"

isProof :: TPTP.Success -> Bool
isProof = \case
  TPTP.UNS -> True
  TPTP.THM -> True
  _ -> False

isSaturation :: TPTP.Success -> Bool
isSaturation = \case
  TPTP.SAT -> True
  TPTP.CSA -> True
  _ -> False

decodeRefutation :: [TPTP.Unit] -> Partial (Refutation Integer)
decodeRefutation units = do
  derivation <- decodeDerivation units
  case unliftRefutation derivation of
    Just refutation -> return refutation
    Nothing -> proofError "malformed input: refutation not found"

decodeDerivation :: [TPTP.Unit] -> Partial (Derivation Integer)
decodeDerivation units = do
  decodedSequents <- traverse decodeSequent units
  let expressions = labeling decodedSequents
  return . evalEnumeration
         . foldM (decodeSequentS expressions) mempty
         $ decodedSequents

decodeSequentS :: Ord n => Map n LogicalExpression -> Derivation Integer ->
                           Sequent n -> Enumeration n (Derivation Integer)
decodeSequentS es d s@(Sequent l i) =
  case find synonymous (antecedents i) of
    Just a  -> alias l a $> d
    Nothing -> addSequent d <$> traverse enumerate s
  where synonymous a = es ! a ~= consequent i

decodeSequent :: TPTP.Unit -> Partial (Sequent TPTP.UnitName)
decodeSequent = \case
  TPTP.Unit name (TPTP.Formula role formula) (Just (source, _)) -> do
    rule <- decodeRule source role (collectParents source)
    expression <- decode formula
    return $ Sequent name (Inference rule expression)
  _ -> proofError "malformed input: expected unit"

collectParents :: TPTP.Source -> [TPTP.UnitName]
collectParents = \case
  TPTP.File{}           -> []
  TPTP.Theory{}         -> []
  TPTP.Creator{}        -> []
  TPTP.Introduced{}     -> []
  TPTP.Inference _ _ ps -> concatMap (\(TPTP.Parent p _) -> collectParents p) ps
  TPTP.UnitSource p     -> [p]
  TPTP.UnknownSource    -> []

decodeRule :: TPTP.Source -> TPTP.Reserved TPTP.Role -> [f] -> Partial (Rule f)
decodeRule s role as = case s of
  TPTP.Theory{}           -> parsingError $ "unsupported unit source " ++ show s
  TPTP.Creator{}          -> parsingError $ "unsupported unit source " ++ show s
  TPTP.UnitSource{}       -> return $ Other "triviality" as
  TPTP.Introduced taut _  -> return $ decodeTautologyRule taut
  TPTP.UnknownSource      -> return $ Unknown as
  TPTP.File{}             -> decodeIntroductionRule role as
  TPTP.Inference rule _ _ -> return $ decodeInferenceRule rule as

decodeTautologyRule :: TPTP.Reserved TPTP.Intro -> Rule f
decodeTautologyRule = \case
  TPTP.Standard TPTP.ByAxiomOfChoice -> AxiomOfChoice
  TPTP.Extended "choice_axiom" -> AxiomOfChoice
  _ -> Axiom

decodeIntroductionRule :: TPTP.Reserved TPTP.Role -> [a] -> Partial (Rule f)
decodeIntroductionRule role as = case (role, as) of
  (TPTP.Standard TPTP.Axiom,      []) -> return Axiom
  (TPTP.Standard TPTP.Conjecture, []) -> return Conjecture
  _ -> proofError $ "unexpected unit role " <> show role

decodeInferenceRule :: TPTP.Atom -> [f] -> Rule f
decodeInferenceRule (TPTP.Atom rule) as = case (rule, as) of
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
  _ -> Other (RuleName rule) as
