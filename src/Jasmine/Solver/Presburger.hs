module Jasmine.Solver.Presburger where

import Jasmine.Solver.Presburger.Internal
import Z.Algo.Function

mkIVar :: MyVar -> PresburgerTermRep
mkIVar x = if x >= theMinNumOfMyVar then IVar x else error "mkIVar: bad individual variable"

mkZero :: PresburgerTermRep
mkZero = Zero

mkSucc :: PresburgerTermRep -> PresburgerTermRep
mkSucc t1 = t1 `seq` Succ t1

mkPlus :: PresburgerTermRep -> PresburgerTermRep -> PresburgerTermRep
mkPlus t1 t2 = t1 `seq` t2 `seq` Plus t1 t2

mkEqnF :: PresburgerTermRep -> PresburgerTermRep -> MyPresburgerFormulaRep
mkEqnF t1 t2 = t1 `seq` t2 `seq` EqnF t1 t2

mkLtnF :: PresburgerTermRep -> PresburgerTermRep -> MyPresburgerFormulaRep
mkLtnF t1 t2 = t1 `seq` t2 `seq` LtnF t1 t2

mkLeqF :: PresburgerTermRep -> PresburgerTermRep -> MyPresburgerFormulaRep
mkLeqF t1 t2 = t1 `seq` t2 `seq` LeqF t1 t2

mkGtnF :: PresburgerTermRep -> PresburgerTermRep -> MyPresburgerFormulaRep
mkGtnF t1 t2 = t1 `seq` t2 `seq` GtnF t1 t2

mkModF :: PresburgerTermRep -> PositiveInteger -> PresburgerTermRep -> MyPresburgerFormulaRep
mkModF t1 r t2 = if r > 0 then t1 `seq` t2 `seq` ModF t1 r t2 else error "mkModF: r must be positive"

mkBotF :: MyPresburgerFormulaRep
mkBotF = ValF False

mkNegF :: MyPresburgerFormulaRep -> MyPresburgerFormulaRep
mkNegF f1 = f1 `seq` NegF f1

mkConF :: MyPresburgerFormulaRep -> MyPresburgerFormulaRep -> MyPresburgerFormulaRep
mkConF f1 f2 = f1 `seq` f2 `seq` ConF f1 f2

mkDisF :: MyPresburgerFormulaRep -> MyPresburgerFormulaRep -> MyPresburgerFormulaRep
mkDisF f1 f2 = f1 `seq` f2 `seq` ConF f1 f2

mkImpF :: MyPresburgerFormulaRep -> MyPresburgerFormulaRep -> MyPresburgerFormulaRep
mkImpF f1 f2 = f1 `seq` f2 `seq` ImpF f1 f2

mkIffF :: MyPresburgerFormulaRep -> MyPresburgerFormulaRep -> MyPresburgerFormulaRep
mkIffF f1 f2 = f1 `seq` f2 `seq` IffF f1 f2

mkAllF :: MyVar -> MyPresburgerFormulaRep -> MyPresburgerFormulaRep
mkAllF y f1 = if y >= theMinNumOfMyVar then f1 `seq` AllF y f1 else error "mkAllF: bad individual variable"

mkExsF :: MyVar -> MyPresburgerFormulaRep -> MyPresburgerFormulaRep
mkExsF y f1 = if y >= theMinNumOfMyVar then f1 `seq` ExsF y f1 else error "mkExsF: bad individual variable"

substitutePresburger :: MyVar -> PresburgerTermRep -> MyPresburgerFormulaRep -> MyPresburgerFormulaRep
substitutePresburger = curry substitute

checkPresburgerFormulaIsSentence :: MyPresburgerFormulaRep -> Bool
checkPresburgerFormulaIsSentence = null . getFVsInPresburgerFormulaRep

checkGivenSentenceIsInTheTheoryOfPresburgerArithmetic :: MyPresburgerFormulaRep -> MyProp
checkGivenSentenceIsInTheTheoryOfPresburgerArithmetic = fromJust . checkTruthValueOfMyPresburgerFormula . eliminateQuantifierReferringToTheBookWrittenByPeterHinman . fmap compilePresburgerTerm
