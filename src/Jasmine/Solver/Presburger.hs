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

type DisjunctionOfConjunctionsOfAtomFormulas = [[AtomFormula]]

type LinearExpression = (MyNat, Map.Map Var PositiveInteger)

data AtomFormula
    = EqF Term Term
    | LtF Term Term
    | CMF Term PositiveInteger Term
    deriving (Eq, Show)

isSentence :: Formula -> Bool
isSentence = Set.null . getFVs

tryEvaluate :: Formula -> Maybe Bool
tryEvaluate = checkTruthValueOfMyPresburgerFormula . fmap compilePresburgerTerm

isInTheory :: Formula -> Bool
isInTheory = fromJust . checkTruthValueOfMyPresburgerFormula . eliminateQuantifierReferringToTheBookWrittenByPeterHinman . fmap compilePresburgerTerm 

applySubstitution :: [(Var, Term)] -> Formula -> Formula
applySubstitution = runFormulaSubst

composeSubstitution :: [(Var, Term)] -> [(Var, Term)] -> [(Var, Term)]
composeSubstitution outer_map inner_map = [ (x, runTermSubst outer_map t) | (x, t) <- inner_map ] ++ outer_map

mkNum :: MyNat -> Term
mkNum n = if n >= 0 then recNat mkZero (const mkSucc) n else error "Jasmine.Solver.Presburger.mkNum> A negative input is given..."

mkIVar :: Var -> Term
mkIVar x = if x >= theMinNumOfMyVar then IVar x else error "Jasmine.Solver.Presburger.mkIVar> A bad individual variable given..."

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
mkModF t1 r t2 = if r > 0 then t1 `seq` t2 `seq` ModF t1 r t2 else error "Jasmine.Solver.Presburger.mkModF> The second input must be positive..."

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
mkAllF y f1 = if y >= theMinNumOfMyVar then f1 `seq` AllF y f1 else error "Jasmine.Solver.Presburger.mkAllF> A bad individual variable is given..."

mkExsF :: Var -> Formula -> Formula
mkExsF y f1 = if y >= theMinNumOfMyVar then f1 `seq` ExsF y f1 else error "Jasmine.Solver.Presburger.mkExsF> A bad individual variable is given..."

destTerm :: Term -> LinearExpression
destTerm = compilePresburgerTerm >>= pure (curry return) <*> getConstantTerm <*> getCoefficients

destFormula :: Formula -> DisjunctionOfConjunctionsOfAtomFormulas
destFormula = makeDNF . simplify . either (\err_msg -> error ("Jasmine.Solver.Presburger.destFormula> " ++ err_msg)) id . toFormulaRep . eliminateQuantifierReferringToTheBookWrittenByPeterHinman . fmap compilePresburgerTerm where
    unNegF :: Formula -> Formula
    unNegF (ValF b) = ValF (not b)
    unNegF (NegF f1) = f1
    unNegF (DisF f1 f2) = mkConF (unNegF f1) (unNegF f2)
    unNegF (ConF f1 f2) = mkDisF (unNegF f1) (unNegF f2)
    unNegF (EqnF t1 t2) = mkDisF (mkLtnF t1 t2) (mkLtnF t2 t1)
    unNegF (LtnF t1 t2) = mkLtnF t2 (mkSucc t1)
    unNegF (LeqF t1 t2) = mkLtnF t2 t1
    unNegF (GtnF t1 t2) = mkLtnF t1 (mkSucc t2)
    unNegF (ModF t1 r t2) = foldr mkDisF mkBotF [ mkModF t1 r (mkPlus t2 (mkNum i)) | i <- [1 .. r - 1] ]
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
    makeDNF :: Formula -> DisjunctionOfConjunctionsOfAtomFormulas
    makeDNF (ValF b) = if b then pure mempty else []
    makeDNF (DisF f1 f2) = makeDNF f1 ++ makeDNF f2
    makeDNF (ConF f1 f2) = pure mappend <*> makeDNF f1 <*> makeDNF f2
    makeDNF (EqnF t1 t2) = pure [EqF t1 t2]
    makeDNF (LtnF t1 t2) = pure [LtF t1 t2]
    makeDNF (LeqF t1 t2) = pure [LtF t1 (mkSucc t2)]
    makeDNF (GtnF t1 t2) = pure [LtF t2 t1]
    makeDNF (ModF t1 r t2) = pure [CMF t1 r t2]
