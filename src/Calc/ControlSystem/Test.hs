module Calc.ControlSystem.Test where

import Calc.ControlSystem.Diagram.Solver
import Calc.ControlSystem.Export
import Calc.ControlSystem.Util
import Data.Maybe
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
        actual = fromJust $ calcDiagram testcase1 ("R", "C")

ans1 :: MyExpr
ans1 = fromJust $ calcDiagram diagram1 ("R", "CR") where
    diagram1 :: Diagram
    diagram1 = Map.fromList
        [ (("R", "__1"), readElemExpr "1")
        , (("__1", "__2"), readElemExpr "Gc(s)")
        , (("__2", "__3"), readElemExpr "G1(s) * G2(s)")
        , (("__3", "__2"), readElemExpr "- H1(s)")
        , (("__3", "__4"), readElemExpr "G3(s)")
        , (("__4", "__1"), readElemExpr "- H2(s)")
        , (("__4", "CR"), readElemExpr "1")
        ]

ans2 :: MyExpr
ans2 = fromJust $ calcDiagram diagram2 ("D", "CD") where
    diagram2 :: Diagram
    diagram2 = Map.fromList
        [ (("D", "__2"), readElemExpr "1")
        , (("__1", "__2"), readElemExpr "G1(s)")
        , (("__2", "__3"), readElemExpr "G2(s)")
        , (("__3", "__1"), readElemExpr "- H1(s)")
        , (("__3", "__4"), readElemExpr "G3(s)")
        , (("__4", "__1"), readElemExpr "- H2(s) * Gc(s)")
        , (("__4", "CD"), readElemExpr "1")
        ]

ans3 :: MyExpr
ans3 = fromJust $ calcDiagram diagram3 ("R", "C") where
    diagram3 :: Diagram
    diagram3 = Map.fromList
        [ (("R", "__1"), readElemExpr "1")
        , (("__1", "__2"), readElemExpr "G1")
        , (("__2", "__3"), readElemExpr "1")
        , (("__3", "__4"), readElemExpr "1")
        , (("__4", "__5"), readElemExpr "G2")
        , (("__4", "__6"), readElemExpr "H1")
        , (("__5", "__2"), readElemExpr "- H2")
        , (("__5", "__6"), readElemExpr "1")
        , (("__6", "__7"), readElemExpr "G3")
        , (("__7", "__8"), readElemExpr "1")
        , (("__7", "C"), readElemExpr "1")
        , (("__8", "__1"), readElemExpr "- 1")
        , (("__8", "__2"), readElemExpr "- H3")
        ]
