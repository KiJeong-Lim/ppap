module Project.A.Go.Shrink where

import qualified Data.List as List

import Project.A.Go.AST

minimalProgram :: Program
minimalProgram = Program [] [SPrintln [EInt 0]]

shrinkProgram :: Program -> [Program]
shrinkProgram program@(Program funcs stmts) = List.nub (filter (/= program) (minimal ++ removed ++ changed)) where
    minimal = [minimalProgram]
    removed = [Program funcs candidate | candidate <- removeOne stmts, not (null candidate)]
    changed = [Program funcs (prefix ++ [stmt'] ++ suffix) | (prefix, stmt, suffix) <- splits stmts, stmt' <- shrinkStmt stmt]

shrinkStmt :: Stmt -> [Stmt]
shrinkStmt stmt
    = case stmt of
        SVar ty name expr -> [SVar ty name expr' | expr' <- shrinkExprAs ty expr]
        SVarZero _ _ -> []
        STypeDecl _ _ -> []
        SShortVar ty name expr -> [SShortVar ty name expr' | expr' <- shrinkExprAs ty expr]
        SShortVarCall _ _ _ -> []
        SAssign name expr -> [SAssign name expr' | expr' <- shrinkExprAs (exprTy expr) expr]
        SAssignCall _ _ _ -> []
        SOpAssign name op expr -> [SOpAssign name op expr' | expr' <- shrinkExprAs (exprTy expr) expr]
        SIndexAssign target index expr -> concat
            [ [SIndexAssign target index' expr | index' <- shrinkExprAs TInt index]
            , [SIndexAssign target index expr' | expr' <- shrinkExprAs (exprTy expr) expr]
            ]
        SDerefAssign target expr -> [SDerefAssign target expr' | expr' <- shrinkExprAs (exprTy expr) expr]
        SBlock stmts -> blockReplacements stmts ++ [SBlock stmts' | stmts' <- shrinkStmtList stmts]
        SIf cond thn els -> concat
            [ blockReplacements thn ++ blockReplacements els
            , [SIf (EBool True) thn els, SIf (EBool False) thn els]
            , [SIf cond' thn els | cond' <- shrinkExprAs TBool cond]
            , [SIf cond thn' els | thn' <- shrinkStmtList thn]
            , [SIf cond thn els' | els' <- shrinkStmtList els]
            ]
        SForBounded name bound body -> concat
            [ blockReplacements body
            , [SForBounded name bound' body | bound' <- shrinkBound bound]
            , [SForBounded name bound body' | body' <- shrinkStmtList body]
            ]
        SPrintln exprs -> [SPrintln exprs' | exprs' <- shrinkExprList exprs]
        SExpr expr -> [SExpr expr' | expr' <- shrinkExpr expr]
        SBlank expr -> [SBlank expr' | expr' <- shrinkExpr expr]
        SReturn exprs -> [SReturn exprs' | exprs' <- shrinkExprList exprs]

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

shrinkExprListAs :: Ty -> [Expr] -> [[Expr]]
shrinkExprListAs ty exprs = shorter ++ changed where
    shorter = [candidate | candidate <- removeOne exprs, not (null candidate)]
    changed = [prefix ++ [expr'] ++ suffix | (prefix, expr, suffix) <- splits exprs, expr' <- shrinkExprAs ty expr]

shrinkExprListTyped :: [Expr] -> [[Expr]]
shrinkExprListTyped exprs = [prefix ++ [expr'] ++ suffix | (prefix, expr, suffix) <- splits exprs, expr' <- shrinkExprAs (exprTy expr) expr]

shrinkExprAs :: Ty -> Expr -> [Expr]
shrinkExprAs ty expr = filter ((== ty) . exprTy) (shrinkExpr expr)

shrinkExpr :: Expr -> [Expr]
shrinkExpr expr
    = case expr of
        EInt n -> smallInts n
        EBool True -> [EBool False]
        EBool False -> []
        EString str -> smallStrings str
        ENil _ -> []
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
        EArrayLit ty exprs -> [EArrayLit ty exprs' | exprs' <- shrinkExprListAs ty exprs]
        ESliceLit ty exprs -> [ESliceLit ty exprs' | exprs' <- shrinkExprListAs ty exprs]
        EStructLit ty fields -> [EStructLit ty fields' | fields' <- shrinkStructFields fields]
        EIndex ty target index -> [EIndex ty target index' | index' <- shrinkExprAs TInt index]
        EField _ target _ -> shrinkExpr target
        ELen arg -> [ELen arg' | arg' <- shrinkExpr arg]
        ECall ty name args -> [ECall ty name args' | args' <- shrinkExprListTyped args]
        EAddr arg -> [EAddr arg' | arg' <- shrinkExpr arg, exprTy arg' == exprTy arg]
        EDeref ty arg -> [EDeref ty arg' | arg' <- shrinkExpr arg, exprTy arg' == exprTy arg]

shrinkStructFields :: [(String, Expr)] -> [[(String, Expr)]]
shrinkStructFields fields = [prefix ++ [(name, expr')] ++ suffix | (prefix, (name, expr), suffix) <- splits fields, expr' <- shrinkExprAs (exprTy expr) expr]

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
literalsOf (TArray _ ty) = [EArrayLit ty []]
literalsOf (TSlice ty) = [ESliceLit ty []]
literalsOf (TPointer _) = []
literalsOf (TNamed _) = []
literalsOf (TStruct _) = []

shrinkBound :: Int -> [Int]
shrinkBound bound = List.nub (filter (/= bound) [0, 1, bound `div` 2])

programNodeCount :: Program -> Int
programNodeCount (Program funcs stmts) = 1 + sum (map funcNodeCount funcs) + sum (map stmtNodeCount stmts)

funcNodeCount :: Func -> Int
funcNodeCount func = 1 + sum (map stmtNodeCount (funcBody func))

stmtNodeCount :: Stmt -> Int
stmtNodeCount stmt
    = case stmt of
        SVar _ _ expr -> 1 + exprNodeCount expr
        SVarZero _ _ -> 1
        STypeDecl _ ty -> 1 + tyNodeCount ty
        SShortVar _ _ expr -> 1 + exprNodeCount expr
        SShortVarCall _ _ args -> 1 + sum (map exprNodeCount args)
        SAssign _ expr -> 1 + exprNodeCount expr
        SAssignCall _ _ args -> 1 + sum (map exprNodeCount args)
        SOpAssign _ _ expr -> 1 + exprNodeCount expr
        SIndexAssign target index expr -> 1 + exprNodeCount target + exprNodeCount index + exprNodeCount expr
        SDerefAssign target expr -> 1 + exprNodeCount target + exprNodeCount expr
        SBlock stmts -> 1 + sum (map stmtNodeCount stmts)
        SIf cond thn els -> 1 + exprNodeCount cond + sum (map stmtNodeCount thn) + sum (map stmtNodeCount els)
        SForBounded _ _ body -> 1 + sum (map stmtNodeCount body)
        SPrintln exprs -> 1 + sum (map exprNodeCount exprs)
        SExpr expr -> 1 + exprNodeCount expr
        SBlank expr -> 1 + exprNodeCount expr
        SReturn exprs -> 1 + sum (map exprNodeCount exprs)

exprNodeCount :: Expr -> Int
exprNodeCount expr
    = case expr of
        EInt _ -> 1
        EBool _ -> 1
        EString _ -> 1
        ENil _ -> 1
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
        EArrayLit _ exprs -> 1 + sum (map exprNodeCount exprs)
        ESliceLit _ exprs -> 1 + sum (map exprNodeCount exprs)
        EStructLit _ fields -> 1 + sum (map (exprNodeCount . snd) fields)
        EIndex _ target index -> 1 + exprNodeCount target + exprNodeCount index
        EField _ target _ -> 1 + exprNodeCount target
        ELen expr -> 1 + exprNodeCount expr
        ECall _ _ args -> 1 + sum (map exprNodeCount args)
        EAddr expr -> 1 + exprNodeCount expr
        EDeref _ expr -> 1 + exprNodeCount expr
    where
        binary lhs rhs = 1 + exprNodeCount lhs + exprNodeCount rhs

tyNodeCount :: Ty -> Int
tyNodeCount TInt = 1
tyNodeCount TBool = 1
tyNodeCount TString = 1
tyNodeCount (TArray _ ty) = 1 + tyNodeCount ty
tyNodeCount (TSlice ty) = 1 + tyNodeCount ty
tyNodeCount (TPointer ty) = 1 + tyNodeCount ty
tyNodeCount (TNamed _) = 1
tyNodeCount (TStruct fields) = 1 + sum (map (tyNodeCount . fst) fields)

removeOne :: [a] -> [[a]]
removeOne [] = []
removeOne (x : xs) = xs : map (x :) (removeOne xs)

splits :: [a] -> [([a], a, [a])]
splits = go [] where
    go _ [] = []
    go prefix (x : xs) = (reverse prefix, x, xs) : go (x : prefix) xs
