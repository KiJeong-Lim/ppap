module Jasmine.Solver.Presburger where

import Jasmine.Solver.Presburger.Internal
import Z.Algo.Function

substitutePresburger :: MyVar -> PresburgerTermRep -> MyPresburgerFormulaRep -> MyPresburgerFormulaRep
substitutePresburger = curry substitute

checkPresburgerFormulaIsSentence :: MyPresburgerFormulaRep -> Bool
checkPresburgerFormulaIsSentence = null . getFVsInPresburgerFormulaRep

checkGivenSentenceIsInTheTheoryOfPresburgerArithmetic :: MyPresburgerFormulaRep -> MyProp
checkGivenSentenceIsInTheTheoryOfPresburgerArithmetic = fromJust . checkTruthValueOfMyPresburgerFormula . eliminateQuantifierReferringToTheBookWrittenByPeterHinman . fmap compilePresburgerTerm

makeNumeral :: MyNat -> PresburgerTermRep
makeNumeral n
    | n < 0 = error "makeNumeral: negative input"
    | otherwise = recNat makeZero (const makeSucc) n

makeIVar :: MyVar -> PresburgerTermRep
makeIVar x = if x >= theMinNumOfMyVar then IVar x else error "makeIVar: bad individual variable"

makeZero :: PresburgerTermRep
makeZero = Zero

makeSucc :: PresburgerTermRep -> PresburgerTermRep
makeSucc t1 = t1 `seq` Succ t1

makePlus :: PresburgerTermRep -> PresburgerTermRep -> PresburgerTermRep
makePlus t1 t2 = t1 `seq` t2 `seq` Plus t1 t2

makeEqnF :: PresburgerTermRep -> PresburgerTermRep -> MyPresburgerFormulaRep
makeEqnF t1 t2 = t1 `seq` t2 `seq` EqnF t1 t2

makeLtnF :: PresburgerTermRep -> PresburgerTermRep -> MyPresburgerFormulaRep
makeLtnF t1 t2 = t1 `seq` t2 `seq` LtnF t1 t2

makeLeqF :: PresburgerTermRep -> PresburgerTermRep -> MyPresburgerFormulaRep
makeLeqF t1 t2 = t1 `seq` t2 `seq` LeqF t1 t2

makeGtnF :: PresburgerTermRep -> PresburgerTermRep -> MyPresburgerFormulaRep
makeGtnF t1 t2 = t1 `seq` t2 `seq` GtnF t1 t2

makeModF :: PresburgerTermRep -> PositiveInteger -> PresburgerTermRep -> MyPresburgerFormulaRep
makeModF t1 r t2 = if r > 0 then t1 `seq` t2 `seq` ModF t1 r t2 else error "makeModF: r must be positive"

makeBotF :: MyPresburgerFormulaRep
makeBotF = ValF False

makeNegF :: MyPresburgerFormulaRep -> MyPresburgerFormulaRep
makeNegF f1 = f1 `seq` NegF f1

makeConF :: MyPresburgerFormulaRep -> MyPresburgerFormulaRep -> MyPresburgerFormulaRep
makeConF f1 f2 = f1 `seq` f2 `seq` ConF f1 f2

makeDisF :: MyPresburgerFormulaRep -> MyPresburgerFormulaRep -> MyPresburgerFormulaRep
makeDisF f1 f2 = f1 `seq` f2 `seq` DisF f1 f2

makeImpF :: MyPresburgerFormulaRep -> MyPresburgerFormulaRep -> MyPresburgerFormulaRep
makeImpF f1 f2 = f1 `seq` f2 `seq` ImpF f1 f2

makeIffF :: MyPresburgerFormulaRep -> MyPresburgerFormulaRep -> MyPresburgerFormulaRep
makeIffF f1 f2 = f1 `seq` f2 `seq` IffF f1 f2

makeAllF :: MyVar -> MyPresburgerFormulaRep -> MyPresburgerFormulaRep
makeAllF y f1 = if y >= theMinNumOfMyVar then f1 `seq` AllF y f1 else error "makeAllF: bad individual variable"

makeExsF :: MyVar -> MyPresburgerFormulaRep -> MyPresburgerFormulaRep
makeExsF y f1 = if y >= theMinNumOfMyVar then f1 `seq` ExsF y f1 else error "makeExsF: bad individual variable"
