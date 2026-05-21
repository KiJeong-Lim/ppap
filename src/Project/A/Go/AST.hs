module Project.A.Go.AST
    ( Ty (..)
    , Expr (..)
    , Stmt (..)
    , Program (..)
    , exprTy
    ) where

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
exprTy expr =
    case expr of
        EInt _ -> TInt
        EBool _ -> TBool
        EString _ -> TString
        EVar ty _ -> ty
        EAdd _ _ -> TInt
        ESub _ _ -> TInt
        EMul _ _ -> TInt
        EDiv _ _ -> TInt
        EMod _ _ -> TInt
        EEq _ _ -> TBool
        ENe _ _ -> TBool
        ELt _ _ -> TBool
        ELe _ _ -> TBool
        EGt _ _ -> TBool
        EGe _ _ -> TBool
        ENot _ -> TBool
        EAnd _ _ -> TBool
        EOr _ _ -> TBool
