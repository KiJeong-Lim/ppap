module Z.Math.Classes where

import GHC.Real

type VarID = String

data ReductionOption
    = ReduceLv1
    | ReduceLv2
    deriving (Eq, Show)

data ExprCall
    = SApp VarID [ExprCall]
    deriving (Eq, Show)

class Functor expr => IsExpr expr where
    evalExpr :: Fractional a => [(ExprCall, expr a)] -> expr a -> a
    reduceExpr :: (Eq a, Num a) => ReductionOption -> expr a -> expr a
    embed :: Num a => a -> expr a
    var :: VarID -> expr a
    getExprRep :: Show a => expr a -> ShowS

_INF_ :: Fractional a => a
_INF_ = fromRational infinity

bindVarsToVals :: (Num a, IsExpr expr) => [(VarID, a)] -> [(ExprCall, expr a)]
bindVarsToVals = foldr go [] where
    go :: (Num a, IsExpr expr) => (VarID, a) -> [(ExprCall, expr a)] -> [(ExprCall, expr a)]
    go (x, v) env = (SApp x [], embed v) : env
