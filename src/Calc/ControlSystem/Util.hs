module Calc.ControlSystem.Util where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Z.Math.Temp

type MyNode = String

type MyExpr = BaseRing Double

type ControlSystem = Map.Map (MyNode, MyNode) MyExpr
