module Project.A.Go.Shrink where

import qualified Data.List as List

import Project.A.Go.AST

minimalProgram :: Program
minimalProgram = Program [SPrintln [EInt 0]]

shrinkProgram :: Program -> [Program]
shrinkProgram program@(Program stmts) = List.nub (filter (/= program) (minimal ++ removed ++ changed)) where
    minimal = [minimalProgram]
    removed = [Program candidate | candidate <- removeOne stmts, not (null candidate)]
    changed = [Program (prefix ++ [stmt'] ++ suffix) | (prefix, stmt, suffix) <- splits stmts, stmt' <- shrinkStmt stmt]

shrinkStmt :: Stmt -> [Stmt]
shrinkStmt stmt
    = case stmt of
        SVar ty name expr -> [SVar ty name expr' | expr' <- shrinkExprAs ty expr]
        SAssign name expr -> [SAssign name expr' | expr' <- shrinkExprAs (exprTy expr) expr]
        SBlock stmts -> blockReplacements stmts ++ [SBlock stmts' | stmts' <- shrinkStmtList stmts]
        SIf cond thn els -> concat
            [ [SBlock thn, SBlock els]
            , [SIf (EBool True) thn els, SIf (EBool False) thn els]
            , [SIf cond' thn els | cond' <- shrinkExprAs TBool cond]
            , [SIf cond thn' els | thn' <- shrinkStmtList thn]
            , [SIf cond thn els' | els' <- shrinkStmtList els]
            ]
        SForBounded name bound body -> concat
            [ [SBlock body]
            , [SForBounded name bound' body | bound' <- shrinkBound bound]
            , [SForBounded name bound body' | body' <- shrinkStmtList body]
            ]
        SPrintln exprs -> [SPrintln exprs' | exprs' <- shrinkExprList exprs]

shrinkStmtList :: [Stmt] -> [[Stmt]]
shrinkStmtList stmts = removed ++ changed where
    removed = removeOne stmts
    changed = [prefix ++ [stmt'] ++ suffix | (prefix, stmt, suffix) <- splits stmts, stmt' <- shrinkStmt stmt]

blockReplacements :: [Stmt] -> [Stmt]
blockReplacements [stmt] = [stmt]
blockReplacements _ = []

shrinkExprList :: [Expr] -> [[Expr]]
shrinkExprList exprs = shorter ++ changed where
    shorter = [candidate | candidate <- removeOne exprs, not (null candidate)]
    changed = [prefix ++ [expr'] ++ suffix | (prefix, expr, suffix) <- splits exprs, expr' <- shrinkExprAs (exprTy expr) expr]

shrinkExprAs :: Ty -> Expr -> [Expr]
shrinkExprAs ty expr = filter ((== ty) . exprTy) (shrinkExpr expr)

shrinkExpr :: Expr -> [Expr]
shrinkExpr expr
    = case expr of
        EInt n -> smallInts n
        EBool True -> [EBool False]
        EBool False -> []
        EString str -> smallStrings str
        EVar ty _ -> literalsOf ty
        EAdd lhs rhs -> intBinary EAdd lhs rhs
        ESub lhs rhs -> intBinary ESub lhs rhs
        EMul lhs rhs -> intBinary EMul lhs rhs
        EDiv lhs rhs -> safeDivLike EDiv lhs rhs
        EMod lhs rhs -> safeDivLike EMod lhs rhs
        EEq lhs rhs -> boolBinary EEq lhs rhs
        ENe lhs rhs -> boolBinary ENe lhs rhs
        ELt lhs rhs -> boolBinary ELt lhs rhs
        ELe lhs rhs -> boolBinary ELe lhs rhs
        EGt lhs rhs -> boolBinary EGt lhs rhs
        EGe lhs rhs -> boolBinary EGe lhs rhs
        ENot arg -> arg : [ENot arg' | arg' <- shrinkExprAs TBool arg]
        EAnd lhs rhs -> lhs : rhs : boolBinary EAnd lhs rhs
        EOr lhs rhs -> lhs : rhs : boolBinary EOr lhs rhs

intBinary :: (Expr -> Expr -> Expr) -> Expr -> Expr -> [Expr]
intBinary con lhs rhs = lhs : rhs : [con lhs' rhs | lhs' <- shrinkExprAs TInt lhs] ++ [con lhs rhs' | rhs' <- shrinkExprAs TInt rhs]

safeDivLike :: (Expr -> Expr -> Expr) -> Expr -> Expr -> [Expr]
safeDivLike con lhs rhs = lhs : [con lhs' rhs | lhs' <- shrinkExprAs TInt lhs] ++ [con lhs rhs' | rhs' <- shrinkNonZeroInt rhs]

boolBinary :: (Expr -> Expr -> Expr) -> Expr -> Expr -> [Expr]
boolBinary con lhs rhs = literalsOf TBool ++ [con lhs' rhs | lhs' <- shrinkExprAs (exprTy lhs) lhs] ++ [con lhs rhs' | rhs' <- shrinkExprAs (exprTy rhs) rhs]

shrinkNonZeroInt :: Expr -> [Expr]
shrinkNonZeroInt expr = filter nonZeroInt (shrinkExprAs TInt expr ++ [EInt 1, EInt (-1)])

nonZeroInt :: Expr -> Bool
nonZeroInt (EInt 0) = False
nonZeroInt _ = True

smallInts :: Int -> [Expr]
smallInts n = [EInt value | value <- [-1, 0, 1], value /= n]

smallStrings :: String -> [Expr]
smallStrings str = [EString value | value <- ["", "a"], value /= str]

literalsOf :: Ty -> [Expr]
literalsOf TInt = [EInt 0, EInt 1, EInt (-1)]
literalsOf TBool = [EBool False, EBool True]
literalsOf TString = [EString "", EString "a"]

shrinkBound :: Int -> [Int]
shrinkBound bound = List.nub (filter (/= bound) [0, 1, bound `div` 2])

programNodeCount :: Program -> Int
programNodeCount (Program stmts) = 1 + sum (map stmtNodeCount stmts)

stmtNodeCount :: Stmt -> Int
stmtNodeCount stmt
    = case stmt of
        SVar _ _ expr -> 1 + exprNodeCount expr
        SAssign _ expr -> 1 + exprNodeCount expr
        SBlock stmts -> 1 + sum (map stmtNodeCount stmts)
        SIf cond thn els -> 1 + exprNodeCount cond + sum (map stmtNodeCount thn) + sum (map stmtNodeCount els)
        SForBounded _ _ body -> 1 + sum (map stmtNodeCount body)
        SPrintln exprs -> 1 + sum (map exprNodeCount exprs)

exprNodeCount :: Expr -> Int
exprNodeCount expr
    = case expr of
        EInt _ -> 1
        EBool _ -> 1
        EString _ -> 1
        EVar _ _ -> 1
        EAdd lhs rhs -> binary lhs rhs
        ESub lhs rhs -> binary lhs rhs
        EMul lhs rhs -> binary lhs rhs
        EDiv lhs rhs -> binary lhs rhs
        EMod lhs rhs -> binary lhs rhs
        EEq lhs rhs -> binary lhs rhs
        ENe lhs rhs -> binary lhs rhs
        ELt lhs rhs -> binary lhs rhs
        ELe lhs rhs -> binary lhs rhs
        EGt lhs rhs -> binary lhs rhs
        EGe lhs rhs -> binary lhs rhs
        ENot arg -> 1 + exprNodeCount arg
        EAnd lhs rhs -> binary lhs rhs
        EOr lhs rhs -> binary lhs rhs
    where
        binary lhs rhs = 1 + exprNodeCount lhs + exprNodeCount rhs

removeOne :: [a] -> [[a]]
removeOne [] = []
removeOne (x : xs) = xs : map (x :) (removeOne xs)

splits :: [a] -> [([a], a, [a])]
splits = go [] where
    go _ [] = []
    go prefix (x : xs) = (reverse prefix, x, xs) : go (x : prefix) xs
