module Project.A.Go.Feature where

import qualified Data.List as List

import Project.A.Go.AST

data Feature
    = UsesIf
    | UsesFor
    | UsesDivision
    | UsesModulo
    | UsesShortCircuit
    | UsesNestedBlock
    | UsesShadowing
    | UsesString
    | UsesMultiplePrint
    | UsesZeroLiteral
    | UsesNegativeLiteral
    deriving (Eq, Ord, Show)

featuresOf :: Program -> [Feature]
featuresOf (Program stmts) = List.nub (concatMap stmtFeatures stmts)

stmtFeatures :: Stmt -> [Feature]
stmtFeatures (SVar _ _ expr) = exprFeatures expr
stmtFeatures (SAssign _ expr) = exprFeatures expr
stmtFeatures (SBlock stmts) = UsesNestedBlock : concatMap stmtFeatures stmts
stmtFeatures (SIf cond thn els) = UsesIf : exprFeatures cond ++ concatMap stmtFeatures (thn ++ els)
stmtFeatures (SForBounded _ _ body) = UsesFor : concatMap stmtFeatures body
stmtFeatures (SPrintln exprs) = (if length exprs > 1 then [UsesMultiplePrint] else []) ++ concatMap exprFeatures exprs

exprFeatures :: Expr -> [Feature]
exprFeatures (EInt n)
    | n == 0 = [UsesZeroLiteral]
    | n < 0 = [UsesNegativeLiteral]
    | otherwise = []
exprFeatures (EBool _)
    = []
exprFeatures (EString _)
    = [UsesString]
exprFeatures (EVar _ _)
    = []
exprFeatures (EAdd lhs rhs)
    = both lhs rhs
exprFeatures (ESub lhs rhs)
    = both lhs rhs
exprFeatures (EMul lhs rhs)
    = both lhs rhs
exprFeatures (EDiv lhs rhs)
    = UsesDivision : both lhs rhs
exprFeatures (EMod lhs rhs)
    = UsesModulo : both lhs rhs
exprFeatures (EEq lhs rhs)
    = both lhs rhs
exprFeatures (ENe lhs rhs)
    = both lhs rhs
exprFeatures (ELt lhs rhs)
    = both lhs rhs
exprFeatures (ELe lhs rhs)
    = both lhs rhs
exprFeatures (EGt lhs rhs)
    = both lhs rhs
exprFeatures (EGe lhs rhs)
    = both lhs rhs
exprFeatures (ENot arg)
    = exprFeatures arg
exprFeatures (EAnd lhs rhs)
    = UsesShortCircuit : both lhs rhs
exprFeatures (EOr lhs rhs)
    = UsesShortCircuit : both lhs rhs

both :: Expr -> Expr -> [Feature]
both lhs rhs = exprFeatures lhs ++ exprFeatures rhs
