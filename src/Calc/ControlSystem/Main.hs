module Calc.ControlSystem.Main where

import Calc.ControlSystem.Read
import Calc.ControlSystem.Util
import qualified Data.Map as Map
import qualified Data.Set as Set
import Z.Math.Scalar

makeJumpTable :: MyNode -> ControlSystem -> Map.Map MyNode MyExpr
makeJumpTable q0 table0 = Map.fromList [ (q, simplExpr (theClosure Map.! (q0, q))) | q <- qs ] where
    qs :: [MyNode]
    qs = Set.toAscList theSetOfNodes where
        theSetOfNodes :: Set.Set MyNode
        theSetOfNodes = Set.unions
            [ Set.singleton q0
            , Set.unions [ Set.fromList [q, p] | ((q, p), e) <- Map.toAscList table0 ]
            ]
    lookTable :: Map.Map (MyNode, MyNode) MyExpr -> (MyNode, MyNode) -> MyExpr
    lookTable table = maybe nullRE id . flip Map.lookup table
    theClosure :: Map.Map (MyNode, MyNode) MyExpr
    theClosure = makeClosure (length qs)
    makeClosure :: Int -> Map.Map (MyNode, MyNode) MyExpr
    makeClosure n
        | n < 0 = undefined
        | n == 0 = Map.fromList (init)
        | n > 0 = Map.fromList (loop (qs !! (n - 1)) (makeClosure (n - 1)))
        where
            init :: [((MyNode, MyNode), MyExpr)]
            init = do
                q1 <- qs
                q2 <- qs
                return
                    ( (q1, q2)
                    , lookTable table0 (q1, q2)
                    )
            loop :: MyNode -> Map.Map (MyNode, MyNode) MyExpr -> [((MyNode, MyNode), MyExpr)]
            loop q table = do
                q1 <- qs
                q2 <- qs
                return
                    ( (q1, q2)
                    , unionRE (lookTable table (q1, q2)) (concatRE (lookTable table (q1, q)) (concatRE (starRE (lookTable table (q, q))) (lookTable table (q, q2))))
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
