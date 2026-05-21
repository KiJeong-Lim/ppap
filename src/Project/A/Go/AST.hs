module Project.A.Go.AST where

data Ty
    = TInt
    | TBool
    | TString
    | TArray Int Ty
    | TSlice Ty
    | TPointer Ty
    | TNamed String
    | TStruct [(Ty, String)]
    deriving (Eq, Ord, Show)

data Expr
    = EInt Int
    | EBool Bool
    | EString String
    | ENil Ty
    | EVar Ty String
    | EAdd Expr Expr
    | ESub Expr Expr
    | EMul Expr Expr
    | EDiv Expr Expr
    | EMod Expr Expr
    | EEq Expr Expr
    | ENe Expr Expr
    | ELt Expr Expr
    | ELe Expr Expr
    | EGt Expr Expr
    | EGe Expr Expr
    | ENot Expr
    | EAnd Expr Expr
    | EOr Expr Expr
    | EArrayLit Ty [Expr]
    | ESliceLit Ty [Expr]
    | EStructLit Ty [(String, Expr)]
    | EIndex Ty Expr Expr
    | EField Ty Expr String
    | ELen Expr
    | ECall Ty String [Expr]
    | EAddr Expr
    | EDeref Ty Expr
    deriving (Eq, Ord, Show)

data Stmt
    = SVar Ty String Expr
    | SVarZero Ty String
    | STypeDecl String Ty
    | SShortVar Ty String Expr
    | SShortVarCall [(Ty, String)] String [Expr]
    | SAssign String Expr
    | SAssignCall [String] String [Expr]
    | SOpAssign String String Expr
    | SIndexAssign Expr Expr Expr
    | SDerefAssign Expr Expr
    | SBlock [Stmt]
    | SIf Expr [Stmt] [Stmt]
    | SForBounded String Int [Stmt]
    | SPrintln [Expr]
    | SExpr Expr
    | SBlank Expr
    | SReturn [Expr]
    deriving (Eq, Ord, Show)

data Func
    = Func
    { funcName :: String
    , funcParams :: [(Ty, String)]
    , funcReturns :: [Ty]
    , funcBody :: [Stmt]
    } deriving (Eq, Ord, Show)

data Program
    = Program [Func] [Stmt]
    deriving (Eq, Ord, Show)

exprTy :: Expr -> Ty
exprTy (EInt _) = TInt
exprTy (EBool _) = TBool
exprTy (EString _) = TString
exprTy (ENil ty) = ty
exprTy (EVar ty _) = ty
exprTy (EAdd _ _) = TInt
exprTy (ESub _ _) = TInt
exprTy (EMul _ _) = TInt
exprTy (EDiv _ _) = TInt
exprTy (EMod _ _) = TInt
exprTy (EEq _ _) = TBool
exprTy (ENe _ _) = TBool
exprTy (ELt _ _) = TBool
exprTy (ELe _ _) = TBool
exprTy (EGt _ _) = TBool
exprTy (EGe _ _) = TBool
exprTy (ENot _) = TBool
exprTy (EAnd _ _) = TBool
exprTy (EOr _ _) = TBool
exprTy (EArrayLit ty exprs) = TArray (length exprs) ty
exprTy (ESliceLit ty _) = TSlice ty
exprTy (EStructLit ty _) = ty
exprTy (EIndex ty _ _) = ty
exprTy (EField ty _ _) = ty
exprTy (ELen _) = TInt
exprTy (ECall ty _ _) = ty
exprTy (EAddr expr) = TPointer (exprTy expr)
exprTy (EDeref ty _) = ty
