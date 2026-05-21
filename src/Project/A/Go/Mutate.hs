module Project.A.Go.Mutate where

import qualified Data.List as List

import Project.A.Go.AST

mutateProgram :: Int -> Program -> Program
mutateProgram seed program = chooseMutation seed (mutationCandidates seed program)

mutationCandidates :: Int -> Program -> [Program]
mutationCandidates seed program@(Program funcs stmts) = List.nub (filter (/= program) (riskPrograms ++ inserted ++ changed)) where
    riskPrograms =
        [ Program funcs (stmts ++ [SPrintln [EDiv (EInt (-7)) (EInt 3)]])
        , Program funcs (stmts ++ [SPrintln [EMod (EInt (-7)) (EInt 3)]])
        , Program funcs (stmts ++ [SIf (EBool True) [SPrintln [EInt 0]] [SPrintln [EInt 1]]])
        ]
    inserted = [Program funcs (prefix ++ [SPrintln [EInt (smallSeedInt seed)]] ++ suffix) | (prefix, suffix) <- insertionSplits stmts]
    changed = [Program funcs (prefix ++ [stmt'] ++ suffix) | (prefix, stmt, suffix) <- splits stmts, stmt' <- mutateStmt stmt]

mutateStmt :: Stmt -> [Stmt]
mutateStmt stmt
    = case stmt of
        SVar ty name expr -> [SVar ty name expr' | expr' <- mutateExpr expr, exprTy expr' == ty]
        SVarZero _ _ -> []
        STypeDecl _ _ -> []
        SShortVar ty name expr -> [SShortVar ty name expr' | expr' <- mutateExpr expr, exprTy expr' == ty]
        SShortVarCall _ _ _ -> []
        SAssign name expr -> [SAssign name expr' | expr' <- mutateExpr expr, exprTy expr' == exprTy expr]
        SAssignCall _ _ _ -> []
        SOpAssign name op expr -> [SOpAssign name op expr' | expr' <- mutateExpr expr, exprTy expr' == exprTy expr]
        SIndexAssign target index expr -> concat
            [ [SIndexAssign target index' expr | index' <- mutateExpr index, exprTy index' == TInt]
            , [SIndexAssign target index expr' | expr' <- mutateExpr expr, exprTy expr' == exprTy expr]
            ]
        SDerefAssign target expr -> [SDerefAssign target expr' | expr' <- mutateExpr expr, exprTy expr' == exprTy expr]
        SBlock stmts -> [SBlock stmts' | stmts' <- mutateStmtList stmts]
        SIf cond thn els -> concat
            [ [SIf (ENot cond) thn els]
            , [SIf cond thn' els | thn' <- mutateStmtList thn]
            , [SIf cond thn els' | els' <- mutateStmtList els]
            ]
        SForBounded name bound body -> concat
            [ [SForBounded name bound' body | bound' <- mutateBound bound]
            , [SForBounded name bound body' | body' <- mutateStmtList body]
            ]
        SPrintln exprs -> [SPrintln exprs' | exprs' <- mutateExprList exprs]
        SExpr expr -> [SExpr expr' | expr' <- mutateExpr expr]
        SBlank expr -> [SBlank expr' | expr' <- mutateExpr expr]
        SReturn exprs -> [SReturn exprs' | exprs' <- mutateExprList exprs]

mutateStmtList :: [Stmt] -> [[Stmt]]
mutateStmtList stmts = inserted ++ changed where
    inserted = [prefix ++ [SPrintln [EInt 0]] ++ suffix | (prefix, suffix) <- insertionSplits stmts]
    changed = [prefix ++ [stmt'] ++ suffix | (prefix, stmt, suffix) <- splits stmts, stmt' <- mutateStmt stmt]

mutateExprList :: [Expr] -> [[Expr]]
mutateExprList exprs = inserted ++ changed where
    inserted = [prefix ++ [EInt 0] ++ suffix | (prefix, suffix) <- insertionSplits exprs]
    changed = [prefix ++ [expr'] ++ suffix | (prefix, expr, suffix) <- splits exprs, expr' <- mutateExpr expr, exprTy expr' == exprTy expr]

mutateExpr :: Expr -> [Expr]
mutateExpr expr
    = case expr of
        EInt n -> [EInt (n - 1), EInt (n + 1), EInt (negate n)]
        EBool flag -> [EBool (not flag)]
        EString str -> [EString (str ++ "a")]
        ENil _ -> []
        EVar ty _ -> literalMutations ty
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
        ENot arg -> [ENot arg' | arg' <- mutateExpr arg, exprTy arg' == TBool]
        EAnd lhs rhs -> boolBinary EAnd lhs rhs
        EOr lhs rhs -> boolBinary EOr lhs rhs
        EArrayLit ty exprs -> [EArrayLit ty exprs' | exprs' <- mutateExprListAs ty exprs]
        ESliceLit ty exprs -> [ESliceLit ty exprs' | exprs' <- mutateExprListAs ty exprs]
        EStructLit ty fields -> [EStructLit ty fields' | fields' <- mutateStructFields fields]
        EIndex ty target index -> [EIndex ty target index' | index' <- mutateExpr index, exprTy index' == TInt]
        EField ty target name -> [EField ty target' name | target' <- mutateExpr target, exprTy target' == exprTy target]
        ELen arg -> [ELen arg' | arg' <- mutateExpr arg]
        ECall ty name args -> [ECall ty name args' | args' <- mutateExprListTyped args]
        EAddr arg -> [EAddr arg' | arg' <- mutateExpr arg, exprTy arg' == exprTy arg]
        EDeref ty arg -> [EDeref ty arg' | arg' <- mutateExpr arg, exprTy arg' == exprTy arg]

intBinary :: (Expr -> Expr -> Expr) -> Expr -> Expr -> [Expr]
intBinary con lhs rhs = [con lhs' rhs | lhs' <- mutateExpr lhs, exprTy lhs' == TInt] ++ [con lhs rhs' | rhs' <- mutateExpr rhs, exprTy rhs' == TInt]

safeDivLike :: (Expr -> Expr -> Expr) -> Expr -> Expr -> [Expr]
safeDivLike con lhs rhs = [con lhs' rhs | lhs' <- mutateExpr lhs, exprTy lhs' == TInt] ++ [con lhs rhs' | rhs' <- mutateExpr rhs, exprTy rhs' == TInt, nonZeroLiteral rhs']

boolBinary :: (Expr -> Expr -> Expr) -> Expr -> Expr -> [Expr]
boolBinary con lhs rhs = [con lhs' rhs | lhs' <- mutateExpr lhs, exprTy lhs' == exprTy lhs] ++ [con lhs rhs' | rhs' <- mutateExpr rhs, exprTy rhs' == exprTy rhs]

literalMutations :: Ty -> [Expr]
literalMutations TInt = [EInt 0, EInt 1, EInt (-1)]
literalMutations TBool = [EBool False, EBool True]
literalMutations TString = [EString "", EString "a"]
literalMutations (TArray _ ty) = [EArrayLit ty []]
literalMutations (TSlice ty) = [ESliceLit ty []]
literalMutations ty@(TPointer _) = [ENil ty]
literalMutations (TNamed _) = []
literalMutations (TStruct _) = []

nonZeroLiteral :: Expr -> Bool
nonZeroLiteral (EInt 0) = False
nonZeroLiteral _ = True

mutateBound :: Int -> [Int]
mutateBound bound = List.nub (filter (>= 0) [bound - 1, bound + 1, 0, 1])

chooseMutation :: Int -> [Program] -> Program
chooseMutation _ [] = Program [] [SPrintln [EInt 0]]
chooseMutation seed programs = programs !! (abs seed `mod` length programs)

smallSeedInt :: Int -> Int
smallSeedInt seed = (seed `mod` 7) - 3

insertionSplits :: [a] -> [([a], [a])]
insertionSplits = go [] where
    go prefix [] = [(reverse prefix, [])]
    go prefix rest@(x : xs) = (reverse prefix, rest) : go (x : prefix) xs

splits :: [a] -> [([a], a, [a])]
splits = go [] where
    go _ [] = []
    go prefix (x : xs) = (reverse prefix, x, xs) : go (x : prefix) xs

mutateExprListAs :: Ty -> [Expr] -> [[Expr]]
mutateExprListAs ty exprs = inserted ++ changed where
    inserted = [prefix ++ [defaultExpr ty] ++ suffix | (prefix, suffix) <- insertionSplits exprs]
    changed = [prefix ++ [expr'] ++ suffix | (prefix, expr, suffix) <- splits exprs, expr' <- mutateExpr expr, exprTy expr' == ty]

mutateExprListTyped :: [Expr] -> [[Expr]]
mutateExprListTyped exprs = [prefix ++ [expr'] ++ suffix | (prefix, expr, suffix) <- splits exprs, expr' <- mutateExpr expr, exprTy expr' == exprTy expr]

defaultExpr :: Ty -> Expr
defaultExpr TInt = EInt 0
defaultExpr TBool = EBool False
defaultExpr TString = EString ""
defaultExpr (TArray _ ty) = EArrayLit ty []
defaultExpr (TSlice ty) = ESliceLit ty []
defaultExpr ty@(TPointer _) = ENil ty
defaultExpr (TNamed name) = EStructLit (TNamed name) []
defaultExpr (TStruct fields) = EStructLit (TStruct fields) []

mutateStructFields :: [(String, Expr)] -> [[(String, Expr)]]
mutateStructFields fields = [prefix ++ [(name, expr')] ++ suffix | (prefix, (name, expr), suffix) <- splits fields, expr' <- mutateExpr expr, exprTy expr' == exprTy expr]
