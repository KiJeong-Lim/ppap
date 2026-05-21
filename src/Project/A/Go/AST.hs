module Project.A.Go.AST where

data Ty
    = TInt
    | TBool
    | TString
    deriving (Eq, Ord, Show)

data Expr
    = EInt Int
    | EBool Bool
    | EString String
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
    deriving (Eq, Ord, Show)

data Stmt
    = SVar Ty String Expr
    | SAssign String Expr
    | SBlock [Stmt]
    | SIf Expr [Stmt] [Stmt]
    | SForBounded String Int [Stmt]
    | SPrintln [Expr]
    deriving (Eq, Ord, Show)

newtype Program
    = Program [Stmt]
    deriving (Eq, Ord, Show)

exprTy :: Expr -> Ty
exprTy (EInt _) = TInt
exprTy (EBool _) = TBool
exprTy (EString _) = TString
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
