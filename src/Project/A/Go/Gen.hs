module Project.A.Go.Gen where

import Control.Monad
import Control.Monad.Trans.State.Strict

import Project.A.Go.AST
import Project.A.Types

type Env = [(Ty, String)]

data GenState
    = GenState
    { gsValue :: Int
    , gsCounter :: Int
    } deriving (Eq, Ord, Show)

constantProgram :: Program
constantProgram = Program [] stageOneBaseStmts

genTestCase :: CaseId -> Seed -> Size -> TestCase Program
genTestCase caseId seed size = TestCase { tcCaseId = caseId, tcSeed = seed, tcSize = size, tcProgram = genProgram seed size, tcInput = genRuntimeInput seed size }

genRuntimeInput :: Seed -> Size -> RuntimeInput
genRuntimeInput _ _ = RuntimeInput { riArgs = [], riStdin = "3\n", riEnv = [] }

genProgram :: Seed -> Size -> Program
genProgram seed size
    | size <= 0 = constantProgram
    | otherwise = evalState (genStageOneProgram size) (initialGenState seed)

genStageOneProgram :: Size -> State GenState Program
genStageOneProgram size = do
    assigns <- replicateM assignmentCount genStageOneAssign
    return (Program [] (SVarZero TInt "x" : assigns ++ [stageOneScanStmt, SPrint [EVar TInt "x"]]))
    where
        assignmentCount :: Int
        assignmentCount = max 1 (min 8 size)

genStageOneAssign :: State GenState Stmt
genStageOneAssign = do
    value <- chooseBetween 0 9
    return (SAssign "x" (EInt value))

stageOneBaseStmts :: [Stmt]
stageOneBaseStmts =
    [ SVarZero TInt "x"
    , SAssign "x" (EInt 0)
    , stageOneScanStmt
    , SPrint [EVar TInt "x"]
    ]

stageOneScanStmt :: Stmt
stageOneScanStmt = SExpr (ECall TInt "fmt.Scan" [EAddr (EVar TInt "x")])

genProgramFull :: Size -> State GenState Program
genProgramFull size = do
    stmts <- genProgramStmts size
    if size >= 4 then
        return (Program helperFuncs (go2cStyleStressStmts ++ stmts))
    else
        return (Program [] stmts)

genProgramStmts :: Size -> State GenState [Stmt]
genProgramStmts size = do
    (decls, env) <- genInitialDecls initialVars
    body <- replicateM statementCount (genStmt env exprDepth)
    return (decls ++ body ++ [SPrintln (map varExpr (reverse env))])
    where
        initialVars :: [(Ty, String)]
        initialVars = take initialCount [(TInt, "x"), (TInt, "y"), (TBool, "ok"), (TString, "msg")]

        initialCount :: Int
        initialCount = max 2 (min 4 (2 + size `div` 2))

        statementCount :: Int
        statementCount = max 1 (min 12 (size + 1))

        exprDepth :: Int
        exprDepth = max 1 (min 4 size)

genInitialDecls :: [(Ty, String)] -> State GenState ([Stmt], Env)
genInitialDecls specs = go [] [] specs where
    go decls env [] = return (reverse decls, env)
    go decls env ((ty, name) : rest) = do
        expr <- genLiteral ty
        go (SVar ty name expr : decls) ((ty, name) : env) rest

genStmt :: Env -> Int -> State GenState Stmt
genStmt env depth = do
    kind <- chooseStmtKind env depth
    case kind of
        0 -> genAssign env depth
        1 -> genIf env depth
        2 -> genFor env depth
        _ -> genPrint env depth

chooseStmtKind :: Env -> Int -> State GenState Int
chooseStmtKind env depth = do
    let assignChoices = if null env then [] else [0, 0, 0]
    let recursiveChoices = if depth <= 1 then [] else [1, 2]
    chooseFrom 4 (assignChoices ++ recursiveChoices ++ [4, 4])

genAssign :: Env -> Int -> State GenState Stmt
genAssign env depth = do
    (ty, name) <- chooseFrom (TInt, "x") env
    expr <- genExpr env ty (depth - 1)
    return (SAssign name expr)

genIf :: Env -> Int -> State GenState Stmt
genIf env depth = do
    cond <- genExpr env TBool (depth - 1)
    thn <- genBranchStmt env (depth - 1)
    els <- genBranchStmt env (depth - 1)
    return (SIf cond [thn] [els])

genBranchStmt :: Env -> Int -> State GenState Stmt
genBranchStmt env depth = do
    kind <- chooseFrom 0 [0, 0, 1, 2]
    case kind of
        0 -> genAssign env depth
        _ -> genPrint env depth

genFor :: Env -> Int -> State GenState Stmt
genFor env _ = do
    (_, target) <- chooseFrom (TInt, "x") (varsOfTy TInt env)
    loopName <- freshName "i"
    bound <- chooseInt 5
    let loopVar = EVar TInt loopName
    let targetVar = EVar TInt target
    return (SForBounded loopName bound [SAssign target (EAdd targetVar loopVar)])

genPrint :: Env -> Int -> State GenState Stmt
genPrint env depth = do
    count <- chooseBetween 1 3
    exprs <- replicateM count (genPrintableExpr env depth)
    return (SPrintln exprs)

genPrintableExpr :: Env -> Int -> State GenState Expr
genPrintableExpr env depth = do
    ty <- chooseFrom TInt [TInt, TBool, TString]
    genExpr env ty depth

genExpr :: Env -> Ty -> Int -> State GenState Expr
genExpr env ty depth
    | depth <= 0 = genAtom env ty
    | otherwise = case ty of
        TInt -> genIntExpr env depth
        TBool -> genBoolExpr env depth
        TString -> genStringExpr env depth
        TArray _ _ -> genAtom env ty
        TSlice _ -> genAtom env ty
        TPointer _ -> genAtom env ty
        TNamed _ -> genAtom env ty
        TStruct _ -> genAtom env ty

genIntExpr :: Env -> Int -> State GenState Expr
genIntExpr env depth = do
    choice <- chooseInt 7
    case choice of
        0 -> genAtom env TInt
        1 -> genIntBin EAdd env depth
        2 -> genIntBin ESub env depth
        3 -> genIntBin EMul env depth
        4 -> genSafeDivLike EDiv env depth
        5 -> genSafeDivLike EMod env depth
        _ -> genAtom env TInt

genIntBin :: (Expr -> Expr -> Expr) -> Env -> Int -> State GenState Expr
genIntBin con env depth = do
    lhs <- genExpr env TInt (depth - 1)
    rhs <- genExpr env TInt (depth - 1)
    return (con lhs rhs)

genSafeDivLike :: (Expr -> Expr -> Expr) -> Env -> Int -> State GenState Expr
genSafeDivLike con env depth = do
    lhs <- genExpr env TInt (depth - 1)
    rhs <- genNonZeroIntLiteral
    return (con lhs rhs)

genBoolExpr :: Env -> Int -> State GenState Expr
genBoolExpr env depth = do
    choice <- chooseInt 9
    case choice of
        0 -> genAtom env TBool
        1 -> genCompare ELt env depth
        2 -> genCompare ELe env depth
        3 -> genCompare EGt env depth
        4 -> genCompare EGe env depth
        5 -> genEqLike EEq env depth
        6 -> genEqLike ENe env depth
        7 -> genBoolBin env depth
        _ -> genNot env depth

genCompare :: (Expr -> Expr -> Expr) -> Env -> Int -> State GenState Expr
genCompare con env depth = do
    lhs <- genExpr env TInt (depth - 1)
    rhs <- genExpr env TInt (depth - 1)
    return (con lhs rhs)

genEqLike :: (Expr -> Expr -> Expr) -> Env -> Int -> State GenState Expr
genEqLike con env depth = do
    ty <- chooseFrom TInt [TInt, TBool, TString]
    lhs <- genExpr env ty (depth - 1)
    rhs <- genExpr env ty (depth - 1)
    return (con lhs rhs)

genBoolBin :: Env -> Int -> State GenState Expr
genBoolBin env depth = do
    con <- chooseFrom EAnd [EAnd, EOr]
    lhs <- genExpr env TBool (depth - 1)
    rhs <- genExpr env TBool (depth - 1)
    return (con lhs rhs)

genNot :: Env -> Int -> State GenState Expr
genNot env depth = do
    arg <- genExpr env TBool (depth - 1)
    return (ENot arg)

genStringExpr :: Env -> Int -> State GenState Expr
genStringExpr env _ = genAtom env TString

genAtom :: Env -> Ty -> State GenState Expr
genAtom env ty = do
    useVar <- chooseInt 2
    case varsOfTy ty env of
        [] -> genLiteral ty
        vars
            | useVar == 0 -> genLiteral ty
            | otherwise -> do
                (_, name) <- chooseFrom (ty, "") vars
                return (EVar ty name)

genLiteral :: Ty -> State GenState Expr
genLiteral TInt = genIntLiteral
genLiteral TBool = do
    n <- chooseInt 2
    return (EBool (n == 0))
genLiteral TString = do
    str <- chooseFrom "" ["", "a", "go", "coq", "seed"]
    return (EString str)
genLiteral (TArray n ty) = do
    exprs <- replicateM n (genLiteral ty)
    return (EArrayLit ty exprs)
genLiteral (TSlice ty) = return (ESliceLit ty [])
genLiteral ty@(TPointer _) = return (ENil ty)
genLiteral ty@(TNamed _) = return (EStructLit ty [])
genLiteral ty@(TStruct _) = return (EStructLit ty [])

genIntLiteral :: State GenState Expr
genIntLiteral = do
    n <- chooseBetween (-12) 24
    return (EInt n)

genNonZeroIntLiteral :: State GenState Expr
genNonZeroIntLiteral = do
    n <- chooseFrom 1 [-7, -3, -1, 1, 2, 3, 5, 8]
    return (EInt n)

helperFuncs :: [Func]
helperFuncs =
    [ Func
        { funcName = "add1"
        , funcParams = [(TInt, "a")]
        , funcReturns = [TInt]
        , funcBody = [SReturn [EAdd (EVar TInt "a") (EInt 1)]]
        }
    , Func
        { funcName = "pair"
        , funcParams = [(TInt, "a")]
        , funcReturns = [TInt, TInt]
        , funcBody = [SReturn [EVar TInt "a", EMul (EVar TInt "a") (EInt 2)]]
        }
    ]

go2cStyleStressStmts :: [Stmt]
go2cStyleStressStmts =
    [ STypeDecl "PairBox" (TStruct [(TInt, "left"), (TInt, "right")])
    , SVarZero (TArray 3 TInt) "arr"
    , SVarZero (TArray 2 (TArray 2 TInt)) "grid"
    , SIndexAssign (EVar (TArray 3 TInt) "arr") (EInt 0) (EInt 7)
    , SShortVar TInt "z" (ECall TInt "add1" [EIndex TInt (EVar (TArray 3 TInt) "arr") (EInt 0)])
    , SIndexAssign (EIndex (TArray 2 TInt) (EVar (TArray 2 (TArray 2 TInt)) "grid") (EInt 0)) (EInt 1) (EVar TInt "z")
    , SShortVarCall [(TInt, "p"), (TInt, "q")] "pair" [EVar TInt "z"]
    , SOpAssign "z" "+=" (EVar TInt "p")
    , SBlank (EVar TInt "q")
    , SShortVar (TSlice TInt) "sl" (ESliceLit TInt [EInt 1, EInt 2, EInt 3])
    , SAssign "sl" (ECall (TSlice TInt) "append" [EVar (TSlice TInt) "sl", EVar TInt "z"])
    , SBlank (ELen (EVar (TSlice TInt) "sl"))
    , SShortVar (TNamed "PairBox") "box" (EStructLit (TNamed "PairBox") [("left", EVar TInt "z"), ("right", EVar TInt "q")])
    , SBlank (EField TInt (EVar (TNamed "PairBox") "box") "left")
    , SShortVar (TPointer TInt) "pz" (EAddr (EVar TInt "z"))
    , SDerefAssign (EVar (TPointer TInt) "pz") (EAdd (EDeref TInt (EVar (TPointer TInt) "pz")) (EInt 1))
    ]

varsOfTy :: Ty -> Env -> Env
varsOfTy ty = filter (\(varTy, _) -> varTy == ty)

varExpr :: (Ty, String) -> Expr
varExpr (ty, name) = EVar ty name

freshName :: String -> State GenState String
freshName prefix = do
    st <- get
    let n = gsCounter st
    put st { gsCounter = n + 1 }
    return (prefix ++ show n)

chooseFrom :: a -> [a] -> State GenState a
chooseFrom fallback [] = return fallback
chooseFrom _ xs = do
    index <- chooseInt (length xs)
    return (xs !! index)

chooseBetween :: Int -> Int -> State GenState Int
chooseBetween low high = do
    n <- chooseInt (high - low + 1)
    return (low + n)

chooseInt :: Int -> State GenState Int
chooseInt limit
    | limit <= 0 = return 0
    | otherwise = do
        raw <- nextRaw
        return (raw `mod` limit)

nextRaw :: State GenState Int
nextRaw = do
    st <- get
    let next = (1103515245 * gsValue st + 12345) `mod` 2147483647
    put st { gsValue = next }
    return next

initialGenState :: Seed -> GenState
initialGenState seed = GenState { gsValue = 1 + (seed `mod` 2147483646), gsCounter = 0 }
