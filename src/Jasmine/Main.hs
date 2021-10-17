module Jasmine.Main where

import Jasmine.PresburgerSolver
import Z.Algo.Function
import Z.System.Shelly

testPresburger :: IO ()
testPresburger = mapM_ (shelly . analyze . getCase) [0 .. 10] where
    getCase :: Int -> MyPresburgerFormulaRep
    getCase 0 = (AllF 1 (AllF 2 (LeqF (Plus (Succ Zero) (IVar 2)) (Plus (IVar 1) (IVar 2)))))
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
    check :: MyPresburgerFormulaRep -> Bool
    check = fromJust . destiny . eliminateQuantifier . fmap compileTerm
    analyze :: MyPresburgerFormulaRep -> String
    analyze f
        | null (getFVs f) = "Presburger> The formula ``" ++ shows f ("\'\' is a " ++ (if check f then "true" else "false") ++ " sentence.")
        | otherwise = "Presburger> The formula ``" ++ shows f "\'\' is not a sentence."

main :: IO ()
main = return ()
