module Jasmine.Solver.Presburger.Test where

import Jasmine.Solver.Presburger
import Z.System.Shelly

testPresburger :: IO ()
testPresburger = mapM_ (shelly . showString "Presburger> " . testCase . getCase) [1 .. 12] where
    getCase :: Int -> Formula
    getCase 1 = (mkAllF 1 (mkAllF 2 (mkEqnF (mkPlus (mkIVar 1) (mkIVar 2)) (mkPlus (mkIVar 2) (mkIVar 1)))))
    getCase 2 = (mkAllF 1 (mkLeqF (mkIVar 1) (mkIVar 1)))
    getCase 3 = (mkAllF 1 (mkAllF 2 (mkNegF (mkConF (mkLeqF (mkIVar 1) (mkIVar 2)) (mkGtnF (mkIVar 1) (mkIVar 2))))))
    getCase 4 = (mkAllF 1 (mkAllF 2 (mkImpF (mkConF (mkLeqF (mkIVar 1) (mkIVar 2)) (mkLeqF (mkIVar 2) (mkIVar 1))) (mkEqnF (mkIVar 1) (mkIVar 2)))))
    getCase 5 = (mkAllF 1 (mkAllF 2 (mkAllF 3 (mkImpF (mkConF (mkLeqF (mkIVar 1) (mkIVar 2)) (mkLeqF (mkIVar 2) (mkIVar 3))) (mkLeqF (mkIVar 1) (mkIVar 3))))))
    getCase 6 = (mkAllF 1 (mkNegF (mkLtnF (mkIVar 1) (mkIVar 1))))
    getCase 7 = (mkAllF 1 (mkImpF (mkLtnF (mkZero) (mkIVar 1)) (mkLtnF (mkIVar 1) (mkPlus (mkIVar 1) (mkIVar 1)))))
    getCase 8 = (mkAllF 1 (mkAllF 2 (mkLeqF (mkIVar 1) (mkPlus (mkIVar 1) (mkIVar 2)))))
    getCase 9 = (mkAllF 1 (mkAllF 2 (mkLeqF (mkIVar 2) (mkPlus (mkIVar 1) (mkIVar 2)))))
    getCase 10 = (mkAllF 1 (mkAllF 2 (mkIffF (mkLeqF (mkPlus (mkSucc (mkZero)) (mkIVar 2)) (mkPlus (mkIVar 1) (mkIVar 2))) (mkNegF (mkEqnF (mkIVar 1) (mkZero))))))
    getCase 11 = (mkAllF 1 (mkAllF 2 (mkLeqF (mkPlus (mkSucc (mkZero)) (mkIVar 2)) (mkPlus (mkIVar 1) (mkIVar 2)))))
    getCase 12 = (mkExsF 1 (mkAllF 2 (mkLtnF (mkIVar 2) (mkIVar 1))))
    testCase :: Formula -> String
    testCase f
        | not (isSentence f) = "The formula ``" ++ shows f "\'\' is not a sentence."
        | isInTheory f = "The formula ``" ++ shows f "\'\' is a true sentence."
        | otherwise = "The formula ``" ++ shows f "\'\' is a false sentence."
