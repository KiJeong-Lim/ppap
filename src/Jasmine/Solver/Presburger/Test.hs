module Jasmine.Solver.Presburger.Test where

import Jasmine.Solver.Presburger.Internal
import Z.Algo.Function
import Z.System.Shelly

testPresburger :: IO ()
testPresburger = mapM_ (shelly . showString "Presburger> " . runCase . getCase) [1 .. 12] where
    getCase :: Int -> MyPresburgerFormulaRep
    getCase 1 = (AllF 1 (AllF 2 (EqnF (Plus (IVar 1) (IVar 2)) (Plus (IVar 2) (IVar 1)))))
    getCase 2 = (AllF 1 (LeqF (IVar 1) (IVar 1)))
    getCase 3 = (AllF 1 (AllF 2 (NegF (ConF (LeqF (IVar 1) (IVar 2)) (GtnF (IVar 1) (IVar 2))))))
    getCase 4 = (AllF 1 (AllF 2 (ImpF (ConF (LeqF (IVar 1) (IVar 2)) (LeqF (IVar 2) (IVar 1))) (EqnF (IVar 1) (IVar 2)))))
    getCase 5 = (AllF 1 (AllF 2 (AllF 3 (ImpF (ConF (LeqF (IVar 1) (IVar 2)) (LeqF (IVar 2) (IVar 3))) (LeqF (IVar 1) (IVar 3))))))
    getCase 6 = (AllF 1 (NegF (LtnF (IVar 1) (IVar 1))))
    getCase 7 = (AllF 1 (ImpF (LtnF (Zero) (IVar 1)) (LtnF (IVar 1) (Plus (IVar 1) (IVar 1)))))
    getCase 8 = (AllF 1 (AllF 2 (LeqF (IVar 1) (Plus (IVar 1) (IVar 2)))))
    getCase 9 = (AllF 1 (AllF 2 (LeqF (IVar 2) (Plus (IVar 1) (IVar 2)))))
    getCase 10 = (AllF 1 (AllF 2 (IffF (LeqF (Plus (Succ (Zero)) (IVar 2)) (Plus (IVar 1) (IVar 2))) (NegF (EqnF (IVar 1) (Zero))))))
    getCase 11 = (AllF 1 (AllF 2 (LeqF (Plus (Succ (Zero)) (IVar 2)) (Plus (IVar 1) (IVar 2)))))
    getCase 12 = (ExsF 1 (AllF 2 (LtnF (IVar 2) (IVar 1))))
    runCase :: MyPresburgerFormulaRep -> String
    runCase f
        | isSentence f = if isInTheory f then "The formula ``" ++ shows f "\'\' is a true sentence." else "The formula ``" ++ shows f "\'\' is a false sentence."
        | otherwise = "The formula ``" ++ shows f "\'\' is not a sentence."
    isSentence :: MyPresburgerFormulaRep -> Bool
    isSentence = null . getFVs
    isInTheory :: MyPresburgerFormulaRep -> Bool
    isInTheory = fromJust . checkTruthValueOfMyPresburgerFormula . eliminateQuantifierReferringToTheBookWrittenByPeterHinman . fmap compilePresburgerTerm
