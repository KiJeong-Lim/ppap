module Calc.ControlSystem.Main where

import Calc.ControlSystem.Read
import Calc.ControlSystem.Util
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Z.Algo.Function
import Z.Math.Temp

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
    theClosure = Map.fromList (foldNat (length qs) init loop) where
        init :: [((MyNode, MyNode), MyExpr)]
        init = do
            q_i <- qs
            q_j <- qs
            return
                ( (q_i, q_j)
                , maybe nullRE id (Map.lookup (q_i, q_j) table0)
                )
        loop :: Int -> [((MyNode, MyNode), MyExpr)] -> [((MyNode, MyNode), MyExpr)]
        loop k mapsto = do
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
        epsilonRE = LitEE 1
        nullRE :: MyExpr
        nullRE = LitEE 0
        unionRE :: MyExpr -> MyExpr -> MyExpr
        unionRE e1 e2 = PlusEE e1 e2
        concatRE :: MyExpr -> MyExpr -> MyExpr
        concatRE e1 e2 = MultEE e1 e2
        starRE :: MyExpr -> MyExpr
        starRE e1 = DivEE (LitEE 1) (MinusEE (LitEE 1) e1)
    simplExpr :: MyExpr -> MyExpr
    simplExpr = id
