module Z.Math.Classes where

import GHC.Real

type VarID = String

type ReductionOption = String

class Functor expr => IsExpr expr where
    evalExpr :: Fractional a => [(VarID, ([VarID], expr a))] -> expr a -> a
    reduceExpr :: (Eq a, Num a) => ReductionOption -> expr a -> expr a
    embedding :: Num a => a -> expr a
    var :: VarID -> expr a

_INF_ :: Fractional a => a
_INF_ = fromRational infinity

bindVarsToVals :: (Num a, IsExpr expr) => [(VarID, a)] -> [(VarID, ([VarID], expr a))]
bindVarsToVals = foldr go [] where
    go :: (Num a, IsExpr expr) => (VarID, a) -> [(VarID, ([VarID], expr a))] -> [(VarID, ([VarID], expr a))]
    go (x, v) env = (x, ([], embedding v)) : env
