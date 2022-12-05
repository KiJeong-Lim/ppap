module Calc.ControlSystem.Test where

import Calc.ControlSystem.Diagram.Solver
import Calc.ControlSystem.Export
import Calc.ControlSystem.Util
import qualified Data.List as List
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Y.Base
import Z.Math.Classes
import Z.Math.V1

testcase1 :: Diagram
testcase1 = Map.fromList
    [ (("R", "__1"), readElemExpr "1")  
    , (("__1", "__2"), readElemExpr "1")
    , (("__2", "__3"), readElemExpr "G1(s)")
    , (("__3", "__4"), readElemExpr "G2(s)")
    , (("__4", "__5"), readElemExpr "G3(s)")
    , (("__5", "__6"), readElemExpr "1")
    , (("__6", "C"), readElemExpr "1")
    , (("__6", "__1"), readElemExpr "- 1")
    , (("__5", "__3"), readElemExpr "- H2(s)")
    , (("__4", "__2"), readElemExpr "H1(s)")
    ]

test1OfControlSystem :: IO ()
test1OfControlSystem
    = do
        putStrLn ("expected = " ++ shows expected "")
        putStrLn ("actual   = " ++ shows actual "")
    where
        expected :: MyExpr
        expected = readElemExpr "G1(s) * G2(s) * G3(s) / (1 - G1(s) * G2(s) * H1(s) + G2(s) * G3(s) * H2(s) + G1(s) * G2(s) * G3(s))"
        actual :: MyExpr
        actual = calcDiagram testcase1 "R" "C"
