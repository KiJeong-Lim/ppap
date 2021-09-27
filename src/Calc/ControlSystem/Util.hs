module Calc.ControlSystem.Util where

import qualified Data.Map as Map
import qualified Data.Set as Set
import Z.Math.Scalar

type MyNode = String

type MyExpr = ElemExpr Double

type ControlSystem = Map.Map (MyNode, MyNode) MyExpr

testcase1 :: ControlSystem
testcase1 = Map.fromList
    [ (("R", "__1"), 1)  
    , (("__1", "__2"), 1)
    , (("__2", "__3"), VarEE "G1")
    , (("__3", "__4"), VarEE "G2")
    , (("__4", "__5"), VarEE "G3")
    , (("__5", "__6"), 1)
    , (("__6", "C"), 1)
    , (("__6", "__1"), negate 1)
    , (("__5", "__3"), negate (VarEE "H2"))
    , (("__4", "__2"), VarEE "H1")
    ]
