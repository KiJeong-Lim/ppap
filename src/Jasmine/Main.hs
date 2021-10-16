module Jasmine.Main where

import Jasmine.PresburgerSolver

testJasmine :: Int -> IO ()
testJasmine = go . getCase where
    getCase :: Int -> Formula
    getCase 1 = (mkAllF 1 (mkAllF 2 (mkEqnF (mkPlus (mkIVar 1) (mkIVar 2)) (mkPlus (mkIVar 2) (mkIVar 1)))))
    getCase 2 = (mkAllF 1 (mkLeqF (mkIVar 1) (mkIVar 1)))
    getCase 3 = (mkAllF 1 (mkAllF 2 (mkNegF (mkConF (mkLeqF (mkIVar 1) (mkIVar 2)) (mkGtnF (mkIVar 1) (mkIVar 2))))))
    getCase 4 = (mkAllF 1 (mkAllF 2 (mkImpF (mkConF (mkLeqF (mkIVar 1) (mkIVar 2)) (mkLeqF (mkIVar 2) (mkIVar 1))) (mkEqnF (mkIVar 1) (mkIVar 2)))))
    getCase 5 = (mkAllF 1 (mkAllF 2 (mkAllF 3 (mkImpF (mkConF (mkLeqF (mkIVar 1) (mkIVar 2)) (mkLeqF (mkIVar 2) (mkIVar 3))) (mkLeqF (mkIVar 1) (mkIVar 3))))))
    getCase 6 = (mkAllF 1 (mkNegF (mkLtnF (mkIVar 1) (mkIVar 1))))
    getCase 7 = (mkAllF 1 (mkImpF (mkLtnF (mkZero) (mkIVar 1)) (mkLtnF (mkIVar 1) (mkPlus (mkIVar 1) (mkIVar 1)))))
    go :: Formula -> IO ()
    go f = putStrLn ("eval `" ++ shows f ("` = " ++ shows (destiny (eliminateQuantifier f)) ""))

main :: IO ()
main = return ()
