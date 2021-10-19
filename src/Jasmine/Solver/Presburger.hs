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

tryEval :: Formula -> Maybe MyProp
tryEval = checkTruthValueOfMyPresburgerFormula . fmap compilePresburgerTerm

applySubst :: [(Var, Term)] -> Formula -> Formula
applySubst = runMySubst . foldr consMySubst nilMySubst

isInTheory :: Formula -> MyProp
isInTheory = fromJust . checkTruthValueOfMyPresburgerFormula . eliminateQuantifierReferringToTheBookWrittenByPeterHinman . fmap compilePresburgerTerm 

eliminateQuantifier :: Formula -> Formula
eliminateQuantifier = fmap discompile . eliminateQuantifierReferringToTheBookWrittenByPeterHinman . fmap compilePresburgerTerm where
    discompile :: PresburgerTerm -> PresburgerTermRep
    discompile (PresburgerTerm con coeffs) = List.foldl' mkPlus (if con < 0 then error "eliminateQuantifier.discompile: constant term must not be negative" else recNat mkZero (const mkSucc) con) [ if n > 0 then recNat (IVar x) (const (flip mkPlus (IVar x))) (n - 1) else error "eliminateQuantifier.discompile: coefficient must be positive" | (x, n) <- Map.toAscList coeffs ]

mkNum :: MyNat -> Term
mkNum n = if n < 0 then error "mkNum: negative input" else recNat mkZero (const mkSucc) n

mkIVar :: Var -> Term
mkIVar x = if x >= theMinNumOfMyVar then IVar x else error "mkIVar: bad individual variable"

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
mkModF t1 r t2 = if r > 0 then t1 `seq` t2 `seq` ModF t1 r t2 else error "mkModF: r must be positive"

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
mkAllF y f1 = if y >= theMinNumOfMyVar then f1 `seq` AllF y f1 else error "mkAllF: bad individual variable"

mkExsF :: Var -> Formula -> Formula
mkExsF y f1 = if y >= theMinNumOfMyVar then f1 `seq` ExsF y f1 else error "mkExsF: bad individual variable"
