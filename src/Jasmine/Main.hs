module Jasmine.Main where

import Jasmine.PresburgerSolver
import Z.System.Shelly

testPresburger :: IO ()
testPresburger = mapM_ (shelly . go . getCase) [1 .. 9] where
    getCase :: Int -> Formula TermRep
    getCase 1 = (AllF 1 (AllF 2 (EqnF (Plus (IVar 1) (IVar 2)) (Plus (IVar 2) (IVar 1)))))
    getCase 2 = (AllF 1 (LeqF (IVar 1) (IVar 1)))
    getCase 3 = (AllF 1 (AllF 2 (NegF (ConF (LeqF (IVar 1) (IVar 2)) (GtnF (IVar 1) (IVar 2))))))
    getCase 4 = (AllF 1 (AllF 2 (ImpF (ConF (LeqF (IVar 1) (IVar 2)) (LeqF (IVar 2) (IVar 1))) (EqnF (IVar 1) (IVar 2)))))
    getCase 5 = (AllF 1 (AllF 2 (AllF 3 (ImpF (ConF (LeqF (IVar 1) (IVar 2)) (LeqF (IVar 2) (IVar 3))) (LeqF (IVar 1) (IVar 3))))))
    getCase 6 = (AllF 1 (NegF (LtnF (IVar 1) (IVar 1))))
    getCase 7 = (AllF 1 (ImpF (LtnF (Zero) (IVar 1)) (LtnF (IVar 1) (Plus (IVar 1) (IVar 1)))))
    getCase 8 = (AllF 1 (AllF 2 (LeqF (IVar 1) (Plus (IVar 1) (IVar 2)))))
    getCase 9 = (AllF 1 (AllF 2 (LeqF (IVar 2) (Plus (IVar 1) (IVar 2)))))
    check :: Formula TermRep -> Maybe Bool
    check = destiny . eliminateQuantifier . fmap runTermRep
    go :: Formula TermRep -> String
    go f = case check f of
        Nothing -> ("Presburger> The formula \'" ++ shows f ("\' is " ++ "not " ++ "a " ++ "sentence."))
        Just b_ -> ("Presburger> The formula \'" ++ shows f ("\' is " ++ "a " ++ showsb b_ "sentence."))
    showsb :: Bool -> ShowS
    showsb b_ = showString (if b_ then "true " else "false ")

main :: IO ()
main = return ()
