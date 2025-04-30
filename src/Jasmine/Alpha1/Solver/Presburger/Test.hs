module Jasmine.Alpha1.Solver.Presburger.Test where

import Jasmine.Alpha1.Solver.Presburger.Internal
import Z.Algo.Function
import Z.System.Shelly

testPresburger :: IO ()
testPresburger = mapM_ (shelly . testCase . at getCase) [1 .. length getCase] where
    getCase :: [MyPresburgerFormulaRep]
    getCase =
        [ (AllF 1 (AllF 2 (EqnF (Plus (IVar 1) (IVar 2)) (Plus (IVar 2) (IVar 1)))))
        , (AllF 1 (LeqF (IVar 1) (IVar 1)))
        , (AllF 1 (AllF 2 (NegF (ConF (LeqF (IVar 1) (IVar 2)) (GtnF (IVar 1) (IVar 2))))))
        , (AllF 1 (AllF 2 (ImpF (ConF (LeqF (IVar 1) (IVar 2)) (LeqF (IVar 2) (IVar 1))) (EqnF (IVar 1) (IVar 2)))))
        , (AllF 1 (AllF 2 (AllF 3 (ImpF (ConF (LeqF (IVar 1) (IVar 2)) (LeqF (IVar 2) (IVar 3))) (LeqF (IVar 1) (IVar 3))))))
        , (AllF 1 (NegF (LtnF (IVar 1) (IVar 1))))
        , (AllF 1 (ImpF (LtnF (Zero) (IVar 1)) (LtnF (IVar 1) (Plus (IVar 1) (IVar 1)))))
        , (AllF 1 (AllF 2 (LeqF (IVar 1) (Plus (IVar 1) (IVar 2)))))
        , (AllF 1 (AllF 2 (LeqF (IVar 2) (Plus (IVar 1) (IVar 2)))))
        , (AllF 1 (AllF 2 (IffF (LeqF (Plus (Succ (Zero)) (IVar 2)) (Plus (IVar 1) (IVar 2))) (NegF (EqnF (IVar 1) (Zero))))))
        , (AllF 1 (AllF 2 (LeqF (Plus (Succ (Zero)) (IVar 2)) (Plus (IVar 1) (IVar 2)))))
        , (ExsF 1 (AllF 2 (LtnF (IVar 2) (IVar 1))))
        ]
    testCase :: MyPresburgerFormulaRep -> String
    testCase f = "Presburger> " ++ testCaseAux1 (isSentence f) where
        testCaseAux1 :: Bool -> String
        testCaseAux1 f_is_a_sentence
            | not f_is_a_sentence = "The formula ``" ++ shows f "\'\' is not a sentence."
            | otherwise = testCaseAux2 (isInTheory f)
        testCaseAux2 :: Bool -> String
        testCaseAux2 f_is_a_theorem
            | f_is_a_theorem = "The formula ``" ++ shows f "\'\' is a true sentence."
            | otherwise = "The formula ``" ++ shows f "\'\' is a false sentence."
    at :: [a] -> Int -> a
    at xs i = xs !! (i - 1)
    isSentence :: MyPresburgerFormulaRep -> Bool
    isSentence = null . getFVs
    isInTheory :: MyPresburgerFormulaRep -> Bool
    isInTheory = fromJust . checkTruthValueOfMyPresburgerFormula . eliminateQuantifierReferringToTheBookWrittenByPeterHinman . fmap compilePresburgerTerm
