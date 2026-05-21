module Project.A.Go.Feature
    ( Feature (..)
    , featuresOf
    ) where

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
featuresOf (Program stmts) =
    List.nub (concatMap stmtFeatures stmts)

stmtFeatures :: Stmt -> [Feature]
stmtFeatures stmt =
    case stmt of
        SVar _ _ expr ->
            exprFeatures expr
        SAssign _ expr ->
            exprFeatures expr
        SBlock stmts ->
            UsesNestedBlock : concatMap stmtFeatures stmts
        SIf cond thn els ->
            UsesIf : exprFeatures cond ++ concatMap stmtFeatures (thn ++ els)
        SForBounded _ _ body ->
            UsesFor : concatMap stmtFeatures body
        SPrintln exprs ->
            (if length exprs > 1 then [UsesMultiplePrint] else []) ++ concatMap exprFeatures exprs

exprFeatures :: Expr -> [Feature]
exprFeatures expr =
    case expr of
        EInt n
            | n == 0 -> [UsesZeroLiteral]
            | n < 0 -> [UsesNegativeLiteral]
            | otherwise -> []
        EBool _ -> []
        EString _ -> [UsesString]
        EVar _ _ -> []
        EAdd lhs rhs -> both lhs rhs
        ESub lhs rhs -> both lhs rhs
        EMul lhs rhs -> both lhs rhs
        EDiv lhs rhs -> UsesDivision : both lhs rhs
        EMod lhs rhs -> UsesModulo : both lhs rhs
        EEq lhs rhs -> both lhs rhs
        ENe lhs rhs -> both lhs rhs
        ELt lhs rhs -> both lhs rhs
        ELe lhs rhs -> both lhs rhs
        EGt lhs rhs -> both lhs rhs
        EGe lhs rhs -> both lhs rhs
        ENot arg -> exprFeatures arg
        EAnd lhs rhs -> UsesShortCircuit : both lhs rhs
        EOr lhs rhs -> UsesShortCircuit : both lhs rhs
  where
    both lhs rhs = exprFeatures lhs ++ exprFeatures rhs
