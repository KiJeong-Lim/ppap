module Z.Math.V1 where

import Data.Ratio
import Y.Base
import Z.Algo.Function
import Z.Math.Classes

type EvalEnv val = [(ExprCall, ElemExpr val)]

data ElemExpr val
    = PluEE (ElemExpr val) (ElemExpr val)
    | NegEE (ElemExpr val)
    | MulEE (ElemExpr val) (ElemExpr val)
    | PosEE (Integer)
    | LitEE (val)
    | VarEE (VarID)
    | AppEE (ElemExpr val) (ElemExpr val)
    deriving ()

instance Show val => Show (ElemExpr val) where
    showsPrec prec = dispatch where
        myPrecIs :: Int -> ShowS -> ShowS
        myPrecIs prec' ss = if prec > prec' then strstr "(" . ss . strstr ")" else ss
        dispatch :: Show val => ElemExpr val -> ShowS
        dispatch (PluEE e1 (NegEE e2)) = myPrecIs 4 (showsPrec 4 e1 . strstr " - " . showsPrec 5 e2)
        dispatch (PluEE e1 e2) = myPrecIs 4 (showsPrec 4 e1 . strstr " + " . showsPrec 5 e2)
        dispatch (NegEE e1) = myPrecIs 6 (strstr "- " . showsPrec 7 e1)
        dispatch (MulEE e1 e2) = myPrecIs 5 (showsPrec 5 e1 . strstr " * " . showsPrec 6 e2)
        dispatch (PosEE n) = myPrecIs 11 (pprint 0 n)
        dispatch (LitEE val) = myPrecIs 11 (showsPrec 11 val)
        dispatch (VarEE var) = myPrecIs 11 (strstr var)
        dispatch (AppEE e1 e2) = fromJust (tryMatchPrimitive (AppEE e1 e2) /> return (myPrecIs 10 (showsPrec 10 e1 . strstr " " . showsPrec 11 e2)))
        tryMatchPrimitive :: Show val => ElemExpr val -> Maybe ShowS
        tryMatchPrimitive (AppEE (VarEE unary_operator) e1) = lookup unary_operator
            [ ("_ABS_", myPrecIs 11 (strstr "| " . showsPrec 0 e1 . strstr " |"))
            ]
        tryMatchPrimitive (AppEE (AppEE (VarEE binary_operator) e1) e2) = lookup binary_operator
            [ ("_DIV_", myPrecIs 5 (showsPrec 5 e1 . strstr " / " . showsPrec 6 e2))
            ]
        tryMatchPrimitive _ = Nothing

instance Functor ElemExpr where
    fmap f (PluEE e1 e2) = PluEE (fmap f e1) (fmap f e2)
    fmap f (NegEE e1) = NegEE (fmap f e1)
    fmap f (MulEE e1 e2) = MulEE (fmap f e1) (fmap f e2)
    fmap f (PosEE n) = PosEE n
    fmap f (LitEE val) = LitEE (f val)
    fmap f (VarEE var) = VarEE var
    fmap f (AppEE e1 e2) = AppEE (fmap f e1) (fmap f e2)

instance Num val => Num (ElemExpr val) where
    e1 + e2 = PluEE e1 e2
    e1 - e2 = PluEE e1 (NegEE e2)
    e1 * e2 = MulEE e1 e2
    negate e1 = NegEE e1
    abs e1 = AppEE (VarEE "_ABS_") e1
    signum e1 = AppEE (AppEE (VarEE "_DIV_") e1) (AppEE (VarEE "_ABS_") e1)
    fromInteger n = case n `compare` 0 of
        LT -> NegEE (PosEE (abs n))
        EQ -> VarEE "0"
        GT -> PosEE n

instance Fractional val => Fractional (ElemExpr val) where
    fromRational r = AppEE (AppEE (VarEE "_DIV_") (fromInteger (numerator r))) (fromInteger (denominator r))
    recip e1 = AppEE (AppEE (VarEE "_DIV_") (PosEE 1)) e1
    e1 / e2 = AppEE (AppEE (VarEE "_DIV_") e1) e2

instance IsExpr ElemExpr where
    evalExpr = evalElemExpr
    reduceExpr = reduceElemExpr
    embed = LitEE
    var = VarEE
    getExprRep = showsPrec 0

evalElemExprWith :: Num val => (EvalEnv val -> ElemExpr val -> ErrMsgM val) -> EvalEnv val -> ElemExpr val -> val
evalElemExprWith = go where
    go :: Num val => (EvalEnv val -> ElemExpr val -> ErrMsgM val) -> EvalEnv val -> ElemExpr val -> val
    go wild_card env (PluEE e1 e2) = go wild_card env e1 + go wild_card env e2
    go wild_card env (NegEE e1) = - go wild_card env e1
    go wild_card env (MulEE e1 e2) = go wild_card env e1 * go wild_card env e2
    go wild_card env (PosEE n) = fromInteger n
    go wild_card env (LitEE v) = v
    go wild_card env e = fromErrMsgM (wild_card env e)

evalElemExpr :: Fractional val => EvalEnv val -> ElemExpr val -> val
evalElemExpr = evalElemExprWith myWildCard where
    myWildCard :: Fractional val => EvalEnv val -> ElemExpr val -> ErrMsgM val
    myWildCard env e = addErrMsg "evalElemExpr" (tryMatchPrimitive env e /> callWith e [] env)
    tryMatchPrimitive :: Fractional val => EvalEnv val -> ElemExpr val -> Maybe val
    tryMatchPrimitive env (VarEE "0") = return 0
    tryMatchPrimitive env (VarEE "0+") = return (1 / _INF_)
    tryMatchPrimitive env (VarEE "0-") = return (- 1 / _INF_)
    tryMatchPrimitive env (VarEE "_INF_") = return _INF_
    tryMatchPrimitive env (AppEE (VarEE "_ABS_") e1) = return (abs (evalElemExpr env e1))
    tryMatchPrimitive env (AppEE (AppEE (VarEE "_DIV_") e1) e2) = return (evalElemExpr env e1 / evalElemExpr env e2)
    tryMatchPrimitive env _ = Nothing
    getDefn :: VarID -> Int -> EvalEnv val -> Maybe ([ExprCall], ElemExpr val)
    getDefn f_lookedup xs_len env = safehd [ (xs, body) | (SApp f xs, body) <- env, f == f_lookedup, length xs == xs_len ]
    callWith :: Fractional val => ElemExpr val -> [ElemExpr val] -> EvalEnv val -> Maybe val
    callWith (AppEE e1 e2) es env = callWith e1 (e2 : es) env
    callWith (VarEE x) es env = do
        (params, body) <- getDefn x (length es) env
        let new_env = zip params es ++ env
        return (evalElemExpr new_env body)
    callWith _ es env = Nothing

reduceElemExpr :: ReductionOption -> ElemExpr val -> ElemExpr val
reduceElemExpr ReduceLv2 = id
reduceElemExpr _ = id
