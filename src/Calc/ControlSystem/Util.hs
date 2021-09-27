module Calc.ControlSystem.Util where

import qualified Data.Map as Map
import qualified Data.Set as Set
import Z.Math.Scalar

type MyNode = String

type MyExpr = ElemExpr Double

type ControlSystem = Map.Map (MyNode, MyNode) MyExpr
