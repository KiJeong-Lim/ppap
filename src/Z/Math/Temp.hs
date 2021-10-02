module Z.Math.Temp where

import Data.Ratio
import Y.Base
import Z.Algo.Function
import Z.Math.Classes

type EvalEnv val = [(VarID, ([VarID], ElemExpr val))]

data ElemExpr val
    = PlusEE (ElemExpr val) (ElemExpr val)
    | MinusEE (ElemExpr val) (ElemExpr val)
    | MultEE (ElemExpr val) (ElemExpr val)
    | NatEE (Integer)
    | LitEE (val)
    | VarEE (VarID)
    | AppEE (ElemExpr val) (ElemExpr val)
    deriving ()

instance Show val => Show (ElemExpr val) where
    showsPrec prec = dispatch where
        myPrecIs :: Int -> ShowS -> ShowS
        myPrecIs prec' ss = if prec > prec' then strstr "(" . ss . strstr ")" else ss
        dispatch :: Show val => ElemExpr val -> ShowS
        dispatch (PlusEE e1 e2) = myPrecIs 4 (showsPrec 4 e1 . strstr " + " . showsPrec 5 e2)
        dispatch (MinusEE e1 e2) = myPrecIs 4 (showsPrec 4 e1 . strstr " - " . showsPrec 5 e2)
        dispatch (MultEE e1 e2) = myPrecIs 5 (showsPrec 5 e1 . strstr " * " . showsPrec 6 e2)
        dispatch (NatEE n) = myPrecIs 11 (showsPrec 11 n)
        dispatch (LitEE val) = myPrecIs 11 (showsPrec 11 val)
        dispatch (VarEE var) = myPrecIs 11 (strstr var)
        dispatch (AppEE e1 e2) = fromJust (tryMatchPrimitive (AppEE e1 e2) /> return (myPrecIs 10 (showsPrec 10 e1 . strstr " " . showsPrec 11 e2)))
        tryMatchPrimitive :: Show val => ElemExpr val -> Maybe ShowS
        tryMatchPrimitive (AppEE (VarEE unary_operator) e1) = lookup unary_operator
            [ ("_ABS_", myPrecIs 11 (strstr "|" . showsPrec 0 e1 . strstr "|"))
            ]
        tryMatchPrimitive (AppEE (AppEE (VarEE binary_operator) e1) e2) = lookup binary_operator
            [ ("_DIV_", myPrecIs 5 (showsPrec 5 e1 . strstr " / " . showsPrec 6 e2))
            ]
        tryMatchPrimitive _ = Nothing

instance Functor ElemExpr where
    fmap f (PlusEE e1 e2) = PlusEE (fmap f e1) (fmap f e2)
    fmap f (MinusEE e1 e2) = MinusEE (fmap f e1) (fmap f e2)
    fmap f (MultEE e1 e2) = MultEE (fmap f e1) (fmap f e2)
    fmap f (NatEE n) = NatEE n
    fmap f (LitEE val) = LitEE (f val)
    fmap f (VarEE var) = VarEE var
    fmap f (AppEE e1 e2) = AppEE (fmap f e1) (fmap f e2)

instance Num val => Num (ElemExpr val) where
    e1 + e2 = PlusEE e1 e2
    e1 - e2 = MinusEE e1 e2 
    e1 * e2 = MultEE e1 e2
    negate e1 = MinusEE (VarEE "0") e1
    abs e1 = AppEE (VarEE "_ABS_") e1
    signum e1 = AppEE (AppEE (VarEE "_DIV_") e1) (AppEE (VarEE "_ABS_") e1)
    fromInteger n = case n `compare` 0 of
        LT -> MinusEE (VarEE "0") (NatEE (abs n))
        EQ -> VarEE "0"
        GT -> NatEE n

instance Fractional val => Fractional (ElemExpr val) where
    fromRational r = AppEE (AppEE (VarEE "_DIV_") (fromInteger (numerator r))) (fromInteger (denominator r))
    recip e1 = AppEE (AppEE (VarEE "_DIV_") (NatEE 1)) e1
    e1 / e2 = AppEE (AppEE (VarEE "_DIV_") e1) e2

instance IsExpr ElemExpr where
    evalExpr = evalElemExpr
    reduceExpr = reduceElemExpr
    embedding = LitEE
    var = VarEE

evalElemExpr :: Fractional val => EvalEnv val -> ElemExpr val -> val
evalElemExpr = go where
    go :: Fractional val => EvalEnv val -> ElemExpr val -> val
    go env (PlusEE e1 e2) = go env e1 + go env e2
    go env (MinusEE e1 e2) = go env e1 - go env e2
    go env (MultEE e1 e2) = go env e1 * go env e2
    go env (NatEE n) = fromInteger n
    go env (LitEE v) = v
    go env e = fromJust (tryMatchPrimitive env e /> callWith e [] env)
    tryMatchPrimitive :: Fractional val => EvalEnv val -> ElemExpr val -> Maybe val
    tryMatchPrimitive env (VarEE "0") = return 0
    tryMatchPrimitive env (VarEE "_INF_") = return _INF_
    tryMatchPrimitive env (AppEE (VarEE "_ABS_") e1) = return (abs (go env e1))
    tryMatchPrimitive env (AppEE (AppEE (VarEE "_DIV_") e1) e2) = return (go env e1 / go env e2)
    tryMatchPrimitive env _ = Nothing
    callWith :: Fractional val => ElemExpr val -> [ElemExpr val] -> EvalEnv val -> Maybe val
    callWith (AppEE e1 e2) es env = callWith e1 (e2 : es) env
    callWith (VarEE x) es env = do
        (params, body) <- lookup x env
        let new_env = [ (param, ([], LitEE (go new_env e))) | (param, e) <- zip params es ] ++ env
        if length params == length es
            then return (go new_env body)
            else fail "In `evalElemExpr': parameters.length /= arguments.length"

reduceElemExpr :: ReductionOption -> ElemExpr val -> ElemExpr val
reduceElemExpr _ = id
