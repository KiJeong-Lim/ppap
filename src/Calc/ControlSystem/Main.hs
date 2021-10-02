module Calc.ControlSystem.Main where

import Calc.ControlSystem.Read
import Calc.ControlSystem.Util
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Z.Algo.Function
import Z.Math.Classes

makePathTable :: MyNode -> ControlSystem -> Map.Map MyNode MyExpr
makePathTable q0 table0 = Map.fromList [ (q, simplExpr (theClosure Map.! (q0, q))) | q <- qs ] where
    qs :: [MyNode]
    qs = Set.toAscList theSetOfNodes where
        theSetOfNodes :: Set.Set MyNode
        theSetOfNodes = Set.unions
            [ Set.singleton q0
            , Set.unions [ Set.fromList [q, p] | (q, p) <- Set.toAscList (Map.keysSet table0) ]
            ]
    theClosure :: Map.Map (MyNode, MyNode) MyExpr
    theClosure = Map.fromList (recNat (length qs) init step) where
        init :: [((MyNode, MyNode), MyExpr)]
        init = do
            q_i <- qs
            q_j <- qs
            return
                ( (q_i, q_j)
                , maybe nullRE id (Map.lookup (q_i, q_j) table0)
                )
        step :: Int -> [((MyNode, MyNode), MyExpr)] -> [((MyNode, MyNode), MyExpr)]
        step k mapsto = do
            let q_k = qs !! k
                table = Map.fromList mapsto
                at idx = table Map.! idx
            q_i <- qs
            q_j <- qs
            return
                ( (q_i, q_j)
                , unionRE (at (q_i, q_j)) (concatRE (at (q_i, q_k)) (concatRE (starRE (at (q_k, q_k))) (at (q_k, q_j))))
                )
        epsilonRE :: MyExpr
        epsilonRE = 1
        nullRE :: MyExpr
        nullRE = 0
        unionRE :: MyExpr -> MyExpr -> MyExpr
        unionRE e1 e2 = e1 + e2
        concatRE :: MyExpr -> MyExpr -> MyExpr
        concatRE e1 e2 = e1 * e2
        starRE :: MyExpr -> MyExpr
        starRE e1 = 1 / (1 - e1)
    simplExpr :: MyExpr -> MyExpr
    simplExpr = reduceExpr ReduceLv1
