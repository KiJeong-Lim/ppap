module Jasmine.Solver.Presburger where

import qualified Data.List as List
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Jasmine.Solver.Presburger.Internal
import Z.Algo.Function

type Var = MyVar

type Term = PresburgerTermRep

type Formula = MyPresburgerFormulaRep

isSentence :: Formula -> Bool
isSentence = Set.null . getFVsInPresburgerFormulaRep

tryEvaluate :: Formula -> Maybe MyProp
tryEvaluate = checkTruthValueOfMyPresburgerFormula . fmap compilePresburgerTerm

isInTheory :: Formula -> MyProp
isInTheory = fromJust . checkTruthValueOfMyPresburgerFormula . eliminateQuantifierReferringToTheBookWrittenByPeterHinman . fmap compilePresburgerTerm 

eliminateQuantifier :: Formula -> Formula
eliminateQuantifier = discompileFormula . eliminateQuantifierReferringToTheBookWrittenByPeterHinman . fmap compilePresburgerTerm where
    discompileFormula :: MyPresburgerFormula -> MyPresburgerFormulaRep
    discompileFormula f = fmap (maybe (error ("Presburger.eliminateQuantifier: The formula ``" ++ shows f "\'\' is ill-formed so not discompilable...")) id . discompileTerm) f
    discompileTerm :: PresburgerTerm -> Maybe PresburgerTermRep
    discompileTerm (PresburgerTerm con coeffs) = pure (List.foldl' mkPlus) <*> (if con < 0 then Nothing else pure (recNat mkZero (const mkSucc) con)) <*> (sequence [ if n > 0 then pure (recNat (IVar x) (const (flip mkPlus (IVar x))) (n - 1)) else Nothing | (x, n) <- Map.toAscList coeffs ])

applySubstitution :: [(Var, Term)] -> Formula -> Formula
applySubstitution = runMySubst . foldr consMySubst nilMySubst

composeSubstitution :: [(Var, Term)] -> [(Var, Term)] -> [(Var, Term)]
composeSubstitution outer_map inner_map = map (fmap (flip applyMySubstToTermRep (foldr consMySubst nilMySubst outer_map))) inner_map ++ outer_map

mkNum :: MyNat -> Term
mkNum n = if n < 0 then error "Presburger.mkNum: A negative input is given..." else recNat mkZero (const mkSucc) n

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
