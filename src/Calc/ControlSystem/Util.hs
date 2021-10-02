module Calc.ControlSystem.Util where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Z.Math.V1

type MyNode = String

type MyExpr = ElemExpr Double

type ControlSystem = Map.Map (MyNode, MyNode) MyExpr
