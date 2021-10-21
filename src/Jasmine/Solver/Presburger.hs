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
    showsPrec prec atom_f = if prec >= 5 then strstr "(" . showsAtomFormula atom_f . strstr ")" else showsAtomFormula atom_f

showsAtomFormula :: AtomFormula -> ShowS
showsAtomFormula (EqF t1 t2) = shows t1 . strstr " = " . shows t2
showsAtomFormula (LtF t1 t2) = shows t1 . strstr " < " . shows t2
showsAtomFormula (CMF t1 r t2) = shows t1 . strstr " ==_{" . shows r . strstr "} " . shows t2

isSentence :: Formula -> Bool
isSentence = Set.null . getFVsInPresburgerFormulaRep

tryEvaluate :: Formula -> Maybe Bool
tryEvaluate = checkTruthValueOfMyPresburgerFormula . fmap compilePresburgerTerm

isInTheory :: Formula -> Bool
isInTheory = fromJust . checkTruthValueOfMyPresburgerFormula . eliminateQuantifierReferringToTheBookWrittenByPeterHinman . fmap compilePresburgerTerm 

applySubstitution :: [(Var, Term)] -> Formula -> Formula
applySubstitution = runMySubst . foldr consMySubst nilMySubst

composeSubstitution :: [(Var, Term)] -> [(Var, Term)] -> [(Var, Term)]
composeSubstitution outer_map inner_map = [ (x, applyMySubstToTermRep t (foldr consMySubst nilMySubst outer_map)) | (x, t) <- inner_map ] ++ outer_map

mkNum :: MyNat -> Term
mkNum n = if n >= 0 then recNat mkZero (const mkSucc) n else error "Presburger.mkNum: A negative input is given..."

mkIVar :: Var -> Term
mkIVar x = if x >= theMinNumOfMyVar then IVar x else error "Presburger.mkIVar: A bad individual variable given..."

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
mkModF t1 r t2 = if r > 0 then t1 `seq` t2 `seq` ModF t1 r t2 else error "Presburger.mkModF: The second input must be positive..."

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
mkAllF y f1 = if y >= theMinNumOfMyVar then f1 `seq` AllF y f1 else error "Presburger.mkAllF: A bad individual variable is given..."

mkExsF :: Var -> Formula -> Formula
mkExsF y f1 = if y >= theMinNumOfMyVar then f1 `seq` ExsF y f1 else error "Presburger.mkExsF: A bad individual variable is given..."

eliminateQuantifier :: Formula -> Formula
eliminateQuantifier = convert . eliminateQuantifierReferringToTheBookWrittenByPeterHinman . fmap compilePresburgerTerm where
    convert :: MyPresburgerFormula -> MyPresburgerFormulaRep
    convert f = maybe (error ("Presburger.eliminateQuantifier: The formula ``" ++ shows f "\'\' is ill-formed...")) id (discompileFormula f)
    discompileTerm :: PresburgerTerm -> Maybe PresburgerTermRep
    discompileTerm (PresburgerTerm con coeffs) = pure (List.foldl' mkPlus) <*> (if con >= 0 then pure (recNat mkZero (const mkSucc) con) else Nothing) <*> (traverse (uncurry $ \var -> \coeff -> if var >= theMinNumOfMyVar && coeff > 0 then pure (recNat (IVar var) (const (flip mkPlus (IVar var))) (coeff - 1)) else Nothing) (Map.toAscList coeffs))
    discompileFormula :: MyPresburgerFormula -> Maybe MyPresburgerFormulaRep
    discompileFormula (ValF b) = pure ValF <*> pure b
    discompileFormula (EqnF t1 t2) = pure EqnF <*> discompileTerm t1 <*> discompileTerm t2
    discompileFormula (LtnF t1 t2) = pure LtnF <*> discompileTerm t1 <*> discompileTerm t2
    discompileFormula (LeqF t1 t2) = pure LeqF <*> discompileTerm t1 <*> discompileTerm t2
    discompileFormula (GtnF t1 t2) = pure GtnF <*> discompileTerm t1 <*> discompileTerm t2
    discompileFormula (ModF t1 r t2) = pure ModF <*> discompileTerm t1 <*> (if r > 0 then pure r else Nothing) <*> discompileTerm t2
    discompileFormula (NegF f1) = pure NegF <*> discompileFormula f1
    discompileFormula (DisF f1 f2) = pure DisF <*> discompileFormula f1 <*> discompileFormula f2
    discompileFormula (ConF f1 f2) = pure ConF <*> discompileFormula f1 <*> discompileFormula f2
    discompileFormula (ImpF f1 f2) = pure ImpF <*> discompileFormula f1 <*> discompileFormula f2
    discompileFormula (IffF f1 f2) = pure IffF <*> discompileFormula f1 <*> discompileFormula f2
    discompileFormula (AllF y f1) = pure AllF <*> (if y >= theMinNumOfMyVar then pure y else Nothing) <*> discompileFormula f1
    discompileFormula (ExsF y f1) = pure ExsF <*> (if y >= theMinNumOfMyVar then pure y else Nothing) <*> discompileFormula f1

toDisjunctiveNormalFormOfAtomFormulae :: Formula -> [[AtomFormula]]
toDisjunctiveNormalFormOfAtomFormulae = toDNF . eliminateQuantifier where
    toDNF :: Formula -> [[AtomFormula]]
    toDNF = makeDNF . simplify where
        runNegation :: Formula -> Formula
        runNegation (ValF b) = mkValF (not b)
        runNegation (EqnF t1 t2) = mkDisF (mkLtnF t1 t2) (mkGtnF t1 t2)
        runNegation (LtnF t1 t2) = mkDisF (mkEqnF t1 t2) (mkGtnF t1 t2)
        runNegation (ModF t1 r t2) = List.foldl' mkDisF mkBotF [ mkModF t1 r (mkPlus t2 (mkNum i)) | i <- [1 .. r - 1] ]
        runNegation (NegF f1) = f1
        runNegation (DisF f1 f2) = mkConF (runNegation f1) (runNegation f2)
        runNegation (ConF f1 f2) = mkDisF (runNegation f1) (runNegation f2)
        simplify :: Formula -> Formula
        simplify (NegF f1) = runNegation (simplify f1)
        simplify (DisF f1 f2) = mkDisF (simplify f1) (simplify f2)
        simplify (ConF f1 f2) = mkConF (simplify f1) (simplify f2)
        simplify (ImpF f1 f2) = mkDisF (runNegation (simplify f1)) (simplify f2)
        simplify (IffF f1 f2) = mkConF (mkDisF (runNegation (simplify f1)) (simplify f2)) (mkDisF (runNegation (simplify f2)) (simplify f1))
        simplify f = f
        makeDNF :: Formula -> [[AtomFormula]]
        makeDNF (ValF b) = if b then pure mempty else []
        makeDNF (EqnF t1 t2) = [[EqF t1 t2]]
        makeDNF (LtnF t1 t2) = [[LtF t1 t2]]
        makeDNF (LeqF t1 t2) = [[LtF t1 t2], [EqF t1 t2]]
        makeDNF (GtnF t1 t2) = [[LtF t2 t1]]
        makeDNF (ModF t1 r t2) = [[CMF t1 r t2]]
        makeDNF (DisF f1 f2) = makeDNF f1 ++ makeDNF f2
        makeDNF (ConF f1 f2) = pure mappend <*> makeDNF f1 <*> makeDNF f2
    mkValF :: Bool -> Formula
    mkValF b = b `seq` ValF b
