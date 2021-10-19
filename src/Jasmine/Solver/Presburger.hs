module Jasmine.Solver.Presburger where

import Jasmine.Solver.Presburger.Internal
import Z.Algo.Function

type Var = MyVar

type TermRep = PresburgerTermRep

type Formula = MyPresburgerFormulaRep

isSentence :: Formula -> Bool
isSentence = null . getFVsInPresburgerFormulaRep

checkGivenSentenceIsInTheory :: Formula -> MyProp
checkGivenSentenceIsInTheory = fromJust . checkTruthValueOfMyPresburgerFormula . eliminateQuantifierReferringToTheBookWrittenByPeterHinman . fmap compilePresburgerTerm

makeSubst :: [(Var, TermRep)] -> MySubst
makeSubst = mkMySubst

applySubst :: MySubst -> Formula -> Formula
applySubst = runMySubst

substituteOne :: Var -> TermRep -> Formula -> Formula
substituteOne = curry substitute

makeNumeral :: MyNat -> TermRep
makeNumeral n = if n < 0 then error "makeNumeral: negative input" else recNat makeZero (const makeSucc) n

makeIVar :: Var -> TermRep
makeIVar x = if x >= theMinNumOfMyVar then IVar x else error "makeIVar: bad individual variable"

makeZero :: TermRep
makeZero = Zero

makeSucc :: TermRep -> TermRep
makeSucc t1 = t1 `seq` Succ t1

makePlus :: TermRep -> TermRep -> TermRep
makePlus t1 t2 = t1 `seq` t2 `seq` Plus t1 t2

makeEqnF :: TermRep -> TermRep -> Formula
makeEqnF t1 t2 = t1 `seq` t2 `seq` EqnF t1 t2

makeLtnF :: TermRep -> TermRep -> Formula
makeLtnF t1 t2 = t1 `seq` t2 `seq` LtnF t1 t2

makeLeqF :: TermRep -> TermRep -> Formula
makeLeqF t1 t2 = t1 `seq` t2 `seq` LeqF t1 t2

makeGtnF :: TermRep -> TermRep -> Formula
makeGtnF t1 t2 = t1 `seq` t2 `seq` GtnF t1 t2

makeModF :: TermRep -> PositiveInteger -> TermRep -> Formula
makeModF t1 r t2 = if r > 0 then t1 `seq` t2 `seq` ModF t1 r t2 else error "makeModF: r must be positive"

makeBotF :: Formula
makeBotF = ValF False

makeNegF :: Formula -> Formula
makeNegF f1 = f1 `seq` NegF f1

makeConF :: Formula -> Formula -> Formula
makeConF f1 f2 = f1 `seq` f2 `seq` ConF f1 f2

makeDisF :: Formula -> Formula -> Formula
makeDisF f1 f2 = f1 `seq` f2 `seq` DisF f1 f2

makeImpF :: Formula -> Formula -> Formula
makeImpF f1 f2 = f1 `seq` f2 `seq` ImpF f1 f2

makeIffF :: Formula -> Formula -> Formula
makeIffF f1 f2 = f1 `seq` f2 `seq` IffF f1 f2

makeAllF :: Var -> Formula -> Formula
makeAllF y f1 = if y >= theMinNumOfMyVar then f1 `seq` AllF y f1 else error "makeAllF: bad individual variable"

makeExsF :: Var -> Formula -> Formula
makeExsF y f1 = if y >= theMinNumOfMyVar then f1 `seq` ExsF y f1 else error "makeExsF: bad individual variable"
