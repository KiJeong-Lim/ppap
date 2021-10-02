module Z.Math.Classes where

import GHC.Real

type VarID = String

type ReductionOption = String

class Functor expr => IsExpr expr where
    evalExpr :: Fractional val => [(VarID, ([VarID], expr val))] -> expr val -> val
    reduceExpr :: (Eq val, Num val) => ReductionOption -> expr val -> expr val
    embedding :: Num val => val -> expr val
    var :: VarID -> expr val

_INF_ :: Fractional a => a
_INF_ = fromRational infinity

bindVarsToVals :: (Num val, IsExpr expr) => [(VarID, val)] -> [(VarID, ([VarID], expr val))]
bindVarsToVals = foldr go [] where
    go :: (Num val, IsExpr expr) => (VarID, val) -> [(VarID, ([VarID], expr val))] -> [(VarID, ([VarID], expr val))]
    go (x, v) env = (x, ([], embedding v)) : env
