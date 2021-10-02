module Z.Math.Classes where

import GHC.Real

type VarID = String

type ReductionOption = String

class Functor expr => IsExpr expr where
    evalExpr :: Fractional literal => [(VarID, ([VarID], expr literal))] -> expr literal -> literal
    reduceExpr :: (Eq literal, Num literal) => ReductionOption -> expr literal -> expr literal
    embedding :: Num literal => literal -> expr literal
    var :: VarID -> expr literal

__INF__ :: Rational
__INF__ = infinity

bindVarsToVals :: (Num literal, IsExpr expr) => [(VarID, literal)] -> [(VarID, ([VarID], expr literal))]
bindVarsToVals = foldr go [] where
    go :: (Num literal, IsExpr expr) => (VarID, literal) -> [(VarID, ([VarID], expr literal))] -> [(VarID, ([VarID], expr literal))]
    go (x, v) env = (x, ([], embedding v)) : env
