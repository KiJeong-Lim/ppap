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

allFeatures :: [Feature]
allFeatures =
    [ UsesIf
    , UsesFor
    , UsesDivision
    , UsesModulo
    , UsesShortCircuit
    , UsesNestedBlock
    , UsesShadowing
    , UsesString
    , UsesMultiplePrint
    , UsesZeroLiteral
    , UsesNegativeLiteral
    ]

featuresOf :: Program -> [Feature]
featuresOf (Program stmts) = List.nub (fst (stmtListFeatures [] [] stmts))

stmtListFeatures :: [[String]] -> [String] -> [Stmt] -> ([Feature], [String])
stmtListFeatures _ current [] = ([], current)
stmtListFeatures outers current (stmt : rest) = (features ++ restFeatures, finalCurrent) where
    (features, nextCurrent) = stmtFeatures outers current stmt
    (restFeatures, finalCurrent) = stmtListFeatures outers nextCurrent rest

stmtFeatures :: [[String]] -> [String] -> Stmt -> ([Feature], [String])
stmtFeatures outers current (SVar _ name expr) = (exprFeatures expr ++ shadowFeatures outers current name, name : current)
stmtFeatures _ current (SAssign _ expr) = (exprFeatures expr, current)
stmtFeatures outers current (SBlock stmts) = (UsesNestedBlock : features, current) where
    (features, _) = stmtListFeatures (current : outers) [] stmts
stmtFeatures outers current (SIf cond thn els) = (UsesIf : exprFeatures cond ++ thnFeatures ++ elsFeatures, current) where
    (thnFeatures, _) = stmtListFeatures (current : outers) [] thn
    (elsFeatures, _) = stmtListFeatures (current : outers) [] els
stmtFeatures outers current (SForBounded name _ body) = (UsesFor : shadowFeatures outers current name ++ bodyFeatures, current) where
    (bodyFeatures, _) = stmtListFeatures (current : outers) [name] body
stmtFeatures _ current (SPrintln exprs) = ((if length exprs > 1 then [UsesMultiplePrint] else []) ++ concatMap exprFeatures exprs, current)

shadowFeatures :: [[String]] -> [String] -> String -> [Feature]
shadowFeatures outers current name
    | name `elem` concat (current : outers) = [UsesShadowing]
    | otherwise = []

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
