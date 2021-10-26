module Jasmine.Solver.Presburger where

import qualified Data.List as List
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Jasmine.Solver.Presburger.Internal
import Y.Base
import Z.Algo.Function

type Var = MyVar

type Term = PresburgerTermRep

type Formula = MyPresburgerFormulaRep

data AtomFormula
    = EqF Term Term
    | LtF Term Term
    | CMF Term PositiveInteger Term
    deriving (Eq)

instance Show AtomFormula where
    showsPrec prec f = if prec >= 5 then strstr "(" . showsAtomFormula f . strstr ")" else showsAtomFormula f
    showList fs = strstr "[" . ppunc ", " (map showsAtomFormula fs) . strstr "]"

isSentence :: Formula -> Bool
isSentence = Set.null . getFVsInPresburgerFormulaRep

tryEvaluate :: Formula -> Maybe Bool
tryEvaluate = checkTruthValueOfMyPresburgerFormula . fmap compilePresburgerTerm

isInTheory :: Formula -> Bool
isInTheory = fromJust . checkTruthValueOfMyPresburgerFormula . eliminateQuantifierReferringToTheBookWrittenByPeterHinman . fmap compilePresburgerTerm 

applySubstitution :: [(Var, Term)] -> Formula -> Formula
applySubstitution = runFormulaSubst

composeSubstitution :: [(Var, Term)] -> [(Var, Term)] -> [(Var, Term)]
composeSubstitution outer_map inner_map = [ (x, runTermSubst outer_map t) | (x, t) <- inner_map ] ++ outer_map

mkNum :: MyNat -> Term
mkNum n = if n >= 0 then recNat mkZero (const mkSucc) n else error "Presburger.mkNum> A negative input is given..."

mkIVar :: Var -> Term
mkIVar x = if x >= theMinNumOfMyVar then IVar x else error "Presburger.mkIVar> A bad individual variable given..."

mkZero :: Term
mkZero = Zero

mkSucc :: Term -> Term
mkSucc t1 = t1 `seq` Succ t1

mkPlus :: Term -> Term -> Term
mkPlus t1 t2 = t1 `seq` t2 `seq` Plus t1 t2

mkEqnF :: Term -> Term -> Formula
mkEqnF t1 t2 = t1 `seq` t2 `seq` EqnF t1 t2

mkLtnF :: Term -> Term -> Formula
mkLtnF t1 t2 = t1 `seq` t2 `seq` LtnF t1 t2

mkLeqF :: Term -> Term -> Formula
mkLeqF t1 t2 = t1 `seq` t2 `seq` LeqF t1 t2

mkGtnF :: Term -> Term -> Formula
mkGtnF t1 t2 = t1 `seq` t2 `seq` GtnF t1 t2

mkModF :: Term -> PositiveInteger -> Term -> Formula
mkModF t1 r t2 = if r > 0 then t1 `seq` t2 `seq` ModF t1 r t2 else error "Presburger.mkModF> The second input must be positive..."

mkBotF :: Formula
mkBotF = ValF False

mkNegF :: Formula -> Formula
mkNegF f1 = f1 `seq` NegF f1

mkConF :: Formula -> Formula -> Formula
mkConF f1 f2 = f1 `seq` f2 `seq` ConF f1 f2

mkDisF :: Formula -> Formula -> Formula
mkDisF f1 f2 = f1 `seq` f2 `seq` DisF f1 f2

mkImpF :: Formula -> Formula -> Formula
mkImpF f1 f2 = f1 `seq` f2 `seq` ImpF f1 f2

mkIffF :: Formula -> Formula -> Formula
mkIffF f1 f2 = f1 `seq` f2 `seq` IffF f1 f2

mkAllF :: Var -> Formula -> Formula
mkAllF y f1 = if y >= theMinNumOfMyVar then f1 `seq` AllF y f1 else error "Presburger.mkAllF> A bad individual variable is given..."

mkExsF :: Var -> Formula -> Formula
mkExsF y f1 = if y >= theMinNumOfMyVar then f1 `seq` ExsF y f1 else error "Presburger.mkExsF> A bad individual variable is given..."

eliminateQuantifier :: Formula -> Formula
eliminateQuantifier = convertToRep . eliminateQuantifierReferringToTheBookWrittenByPeterHinman . fmap compilePresburgerTerm where
    discompileTerm :: PresburgerTerm -> Maybe PresburgerTermRep
    discompileTerm (PresburgerTerm con coeffs) = pure (List.foldl' mkPlus) <*> (if con >= 0 then pure (recNat mkZero (const mkSucc) con) else Nothing) <*> (traverse (uncurry $ \var -> \coeff -> if var >= theMinNumOfMyVar && coeff > 0 then pure (recNat (mkIVar var) (const (flip mkPlus (mkIVar var))) (coeff - 1)) else Nothing) (Map.toAscList coeffs))
    discompileFormula :: MyPresburgerFormula -> Maybe MyPresburgerFormulaRep
    discompileFormula (ValF b) = pure mkValF <*> pure b
    discompileFormula (EqnF t1 t2) = pure mkEqnF <*> discompileTerm t1 <*> discompileTerm t2
    discompileFormula (LtnF t1 t2) = pure mkLtnF <*> discompileTerm t1 <*> discompileTerm t2
    discompileFormula (LeqF t1 t2) = pure mkLeqF <*> discompileTerm t1 <*> discompileTerm t2
    discompileFormula (GtnF t1 t2) = pure mkGtnF <*> discompileTerm t1 <*> discompileTerm t2
    discompileFormula (ModF t1 r t2) = pure mkModF <*> discompileTerm t1 <*> (if r > 0 then pure r else Nothing) <*> discompileTerm t2
    discompileFormula (NegF f1) = pure mkNegF <*> discompileFormula f1
    discompileFormula (DisF f1 f2) = pure mkDisF <*> discompileFormula f1 <*> discompileFormula f2
    discompileFormula (ConF f1 f2) = pure mkConF <*> discompileFormula f1 <*> discompileFormula f2
    discompileFormula (ImpF f1 f2) = pure mkImpF <*> discompileFormula f1 <*> discompileFormula f2
    discompileFormula (IffF f1 f2) = pure mkIffF <*> discompileFormula f1 <*> discompileFormula f2
    discompileFormula (AllF y f1) = pure mkAllF <*> (if y >= theMinNumOfMyVar then pure y else Nothing) <*> discompileFormula f1
    discompileFormula (ExsF y f1) = pure mkExsF <*> (if y >= theMinNumOfMyVar then pure y else Nothing) <*> discompileFormula f1
    convertToRep :: MyPresburgerFormula -> MyPresburgerFormulaRep
    convertToRep f = maybe (error ("Presburger.eliminateQuantifier> The formula ``" ++ shows f "\'\' is ill-formed...")) id (discompileFormula f)
    mkValF :: Bool -> Formula
    mkValF b = b `seq` ValF b

destTerm :: Term -> (Map.Map Var PositiveInteger, MyNat)
destTerm = fmap (pure (curry id) <*> getCoefficients <*> getConstantTerm) compilePresburgerTerm

destFormula :: Formula -> [[AtomFormula]]
destFormula = makeDNF . simplify . eliminateQuantifier where
    unNegF :: Formula -> Formula
    unNegF (ValF b) = mkValF (not b)
    unNegF (NegF f1) = f1
    unNegF (DisF f1 f2) = mkConF (unNegF f1) (unNegF f2)
    unNegF (ConF f1 f2) = mkDisF (unNegF f1) (unNegF f2)
    unNegF atom_f = mkNegF atom_f
    unImpF :: Formula -> Formula -> Formula
    unImpF f1 f2 = mkDisF (unNegF f1) f2
    unIffF :: Formula -> Formula -> Formula
    unIffF f1 f2 = mkConF (unImpF f1 f2) (unImpF f2 f1)
    simplify :: Formula -> Formula
    simplify (NegF f1) = unNegF (simplify f1)
    simplify (DisF f1 f2) = mkDisF (simplify f1) (simplify f2)
    simplify (ConF f1 f2) = mkConF (simplify f1) (simplify f2)
    simplify (ImpF f1 f2) = unImpF (simplify f1) (simplify f2)
    simplify (IffF f1 f2) = unIffF (simplify f1) (simplify f2)
    simplify f = f
    makeDNF :: Formula -> [[AtomFormula]]
    makeDNF (ValF b) = if b then pure mempty else []
    makeDNF (DisF f1 f2) = makeDNF f1 ++ makeDNF f2
    makeDNF (ConF f1 f2) = pure mappend <*> makeDNF f1 <*> makeDNF f2
    makeDNF (NegF atom_f) = negOf atom_f
    makeDNF atom_f = posOf atom_f
    posOf :: Formula -> [[AtomFormula]]
    posOf (EqnF t1 t2) = pure [EqF t1 t2]
    posOf (LtnF t1 t2) = pure [LtF t1 t2]
    posOf (LeqF t1 t2) = pure [LtF t1 (mkSucc t2)]
    posOf (GtnF t1 t2) = pure [LtF t2 t1]
    posOf (ModF t1 r t2) = pure [CMF t1 r t2]
    negOf :: Formula -> [[AtomFormula]]
    negOf (EqnF t1 t2) = pure [LtF t1 t2] ++ pure [LtF t2 t1]
    negOf (LtnF t1 t2) = pure [LtF t2 (mkSucc t1)]
    negOf (LeqF t1 t2) = pure [LtF t2 t1]
    negOf (GtnF t1 t2) = pure [LtF t1 (mkSucc t2)]
    negOf (ModF t1 r t2) = [1 .. r - 1] >>= (\i -> pure [CMF t1 r (mkPlus t2 (mkNum i))])
    mkValF :: Bool -> Formula
    mkValF b = b `seq` ValF b

showsAtomFormula :: AtomFormula -> ShowS
showsAtomFormula (EqF t1 t2) = shows t1 . strstr " = " . shows t2
showsAtomFormula (LtF t1 t2) = shows t1 . strstr " < " . shows t2
showsAtomFormula (CMF t1 r t2) = shows t1 . strstr " ==_{" . shows r . strstr "} " . shows t2
