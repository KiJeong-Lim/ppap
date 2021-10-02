module Calc.ControlSystem.Test where

import Calc.ControlSystem.Main
import Calc.ControlSystem.Read
import Calc.ControlSystem.Util
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Z.Math.Classes

testcase1 :: ControlSystem
testcase1 = Map.fromList
    [ (("R", "__1"), 1)  
    , (("__1", "__2"), 1)
    , (("__2", "__3"), var "G1")
    , (("__3", "__4"), var "G2")
    , (("__4", "__5"), var "G3")
    , (("__5", "__6"), 1)
    , (("__6", "C"), 1)
    , (("__6", "__1"), negate 1)
    , (("__5", "__3"), negate (var "H2"))
    , (("__4", "__2"), var "H1")
    ]

test1OfControlSystemAux :: Double -> Double -> Double -> Double -> Double -> IO ()
test1OfControlSystemAux _G1 _G2 _G3 _H1 _H2
    = do
        putStrLn ("expected = " ++ show expected)
        putStrLn ("actual   = " ++ show actual)
    where
        expected :: Double
        expected = (_G1 * _G2 * _G3) / (1 - _G1 * _G2 * _H1 + _G2 * _G3 * _H2 + _G1 * _G2 * _G3)
        actual :: Double
        actual = evalExpr (bindVarsToVals [("G1", _G1), ("G2", _G2), ("G3", _G3), ("H1", _H1), ("H2", _H2)]) (makePathTable "R" testcase1 Map.! "C")

test1OfControlSystem :: IO ()
test1OfControlSystem = test1OfControlSystemAux 0.1 0.2 0.3 0.4 0.5
