module Jasmine.Main where

import Jasmine.PresburgerSolver

testJasmine :: Int -> IO ()
testJasmine = print . destiny . eliminateQuantifier . go where
    go :: Int -> Formula
    go 1 = (mkAllF 1 (mkAllF 2 (mkEqnF (mkPlus (mkIVar 1) (mkIVar 2)) (mkPlus (mkIVar 2) (mkIVar 1)))))
    go 2 = (mkAllF 1 (mkLeqF (mkIVar 1) (mkIVar 1)))
    go 3 = (mkAllF 1 (mkAllF 2 (mkNegF (mkConF (mkLeqF (mkIVar 1) (mkIVar 2)) (mkGtnF (mkIVar 1) (mkIVar 2))))))
    go 4 = (mkAllF 1 (mkAllF 2 (mkImpF (mkConF (mkLeqF (mkIVar 1) (mkIVar 2)) (mkLeqF (mkIVar 2) (mkIVar 1))) (mkEqnF (mkIVar 1) (mkIVar 2)))))
    go 5 = (mkAllF 1 (mkAllF 2 (mkAllF 3 (mkImpF (mkConF (mkLeqF (mkIVar 1) (mkIVar 2)) (mkLeqF (mkIVar 2) (mkIVar 3))) (mkLeqF (mkIVar 1) (mkIVar 3))))))
    go 6 = (mkAllF 1 (mkNegF (mkLtnF (mkIVar 1) (mkIVar 1))))
    go 7 = (mkAllF 1 (mkImpF (mkLtnF (mkZero) (mkIVar 1)) (mkLtnF (mkIVar 1) (mkPlus (mkIVar 1) (mkIVar 1)))))

main :: IO ()
main = return ()
