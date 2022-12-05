module Calc.ControlSystem.Diagram.Solver where

import Calc.ControlSystem.Util
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Z.Algo.Function
import Z.Math.Classes

calcDiagram :: Diagram -> (MyNode, MyNode) -> Maybe MyExpr
calcDiagram diag (from, to) = reduceExpr ReduceLv2 <$> to `Map.lookup` makePathTable from diag

makePathTable :: MyNode -> Diagram -> Map.Map MyNode MyExpr
makePathTable q0 table0 = Map.fromAscList [ (q, theClosure Map.! (q0, q)) | q <- qs ] where
    qs :: [MyNode]
    qs = Set.toAscList theSetOfNodes where
        theSetOfNodes :: Set.Set MyNode
        theSetOfNodes = Set.unions
            [ Set.singleton q0
            , Set.unions
                [ Set.fromList [q, p]
                | (q, p) <- Set.toAscList (Map.keysSet table0)
                ]
            ]
    theClosure :: Map.Map (MyNode, MyNode) MyExpr
    theClosure = refine (recNat myInit myStep (length qs)) where
        refine :: [((MyNode, MyNode), MyExpr)] -> Map.Map (MyNode, MyNode) MyExpr
        refine = Map.map (reduceExpr ReduceLv1) . Map.fromList
        at :: Map.Map (MyNode, MyNode) MyExpr -> (MyNode, MyNode) -> MyExpr
        at = curry (maybe nullRE id . uncurry (flip Map.lookup))
        myInit :: [((MyNode, MyNode), MyExpr)]
        myInit = do
            q_i <- qs
            q_j <- qs
            return
                ( (q_i, q_j)
                , table0 `at` (q_i, q_j)
                )
        myStep :: Int -> [((MyNode, MyNode), MyExpr)] -> [((MyNode, MyNode), MyExpr)]
        myStep k prev = do
            let q_k = qs !! k
                table = refine prev
            q_i <- qs
            q_j <- qs
            return
                ( (q_i, q_j)
                , unionRE (table `at` (q_i, q_j)) (concatRE (table `at` (q_i, q_k)) (concatRE (starRE (table `at` (q_k, q_k))) (table `at` (q_k, q_j))))
                )
        unionRE :: MyExpr -> MyExpr -> MyExpr
        unionRE e1 e2 = e1 + e2
        nullRE :: MyExpr
        nullRE = 0
        concatRE :: MyExpr -> MyExpr -> MyExpr
        concatRE e1 e2 = e1 * e2
        epsilonRE :: MyExpr
        epsilonRE = 1
        starRE :: MyExpr -> MyExpr
        starRE e1 = 1 / (1 - e1)
