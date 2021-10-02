module Z.Math.Temp where

import qualified Data.Map.Strict as Map
import GHC.Real
import Y.Base
import Z.Algo.Function

type VarID = String

type EvalEnv val = [(VarID, ([VarID], BaseRing val))]

type ReductionOption = String

data BaseRing val
    = PlusEE (BaseRing val) (BaseRing val)
    | MinusEE (BaseRing val) (BaseRing val)
    | MultEE (BaseRing val) (BaseRing val)
    | NatEE (Integer)
    | LitEE (val)
    | VarEE (VarID)
    | AppEE (BaseRing val) (BaseRing val)
    deriving ()

instance Show val => Show (BaseRing val) where
    showsPrec prec = dispatch where
        myPrecIs :: Int -> ShowS -> ShowS
        myPrecIs prec' ss = if prec > prec' then strstr "(" . ss . strstr ")" else ss
        dispatch :: Show val => BaseRing val -> ShowS
        dispatch (PlusEE e1 e2) = myPrecIs 4 (showsPrec 4 e1 . strstr " + " . showsPrec 5 e2)
        dispatch (MinusEE e1 e2) = myPrecIs 4 (showsPrec 4 e1 . strstr " - " . showsPrec 5 e2)
        dispatch (MultEE e1 e2) = myPrecIs 5 (showsPrec 5 e1 . strstr " * " . showsPrec 6 e2)
        dispatch (NatEE n) = myPrecIs 11 (showsPrec 11 n)
        dispatch (LitEE val) = myPrecIs 11 (showsPrec 11 val)
        dispatch (VarEE var) = myPrecIs 11 (strstr var)
        dispatch (AppEE e1 e2) = fromJust (tryMatchPrimitive (AppEE e1 e2) /> return (myPrecIs 10 (showsPrec 10 e1 . strstr " " . showsPrec 11 e2)))
        tryMatchPrimitive :: Show val => BaseRing val -> Maybe ShowS
        tryMatchPrimitive (AppEE (VarEE unary_operator) e1) = lookup unary_operator
            [ ("__ABS__", myPrecIs 11 (strstr "|" . showsPrec 0 e1 . strstr "|"))
            ]
        tryMatchPrimitive (AppEE (AppEE (VarEE binary_operator) e1) e2) = lookup binary_operator
            [ ("__DIV__", myPrecIs 5 (showsPrec 5 e1 . strstr " / " . showsPrec 6 e2))
            ]
        tryMatchPrimitive _ = Nothing

instance Functor BaseRing where
    fmap f (PlusEE e1 e2) = PlusEE (fmap f e1) (fmap f e2)
    fmap f (MinusEE e1 e2) = MinusEE (fmap f e1) (fmap f e2)
    fmap f (MultEE e1 e2) = MultEE (fmap f e1) (fmap f e2)
    fmap f (NatEE n) = NatEE n
    fmap f (LitEE val) = LitEE (f val)
    fmap f (VarEE var) = VarEE var
    fmap f (AppEE e1 e2) = AppEE (fmap f e1) (fmap f e2)

instance Num val => Num (BaseRing val) where
    e1 + e2 = PlusEE e1 e2
    e1 - e2 = MinusEE e1 e2 
    e1 * e2 = MultEE e1 e2
    negate e1 = MinusEE (VarEE "0") e1
    abs e1 = AppEE (VarEE "__ABS__") e1
    signum e1 = AppEE (AppEE (VarEE "__DIV__") e1) (AppEE (VarEE "__ABS__") e1)
    fromInteger n = case n `compare` 0 of
        LT -> MinusEE (VarEE "0") (NatEE (abs n))
        EQ -> VarEE "0"
        GT -> NatEE n

instance Fractional val => Fractional (BaseRing val) where
    fromRational r = AppEE (AppEE (VarEE "__DIV__") (fromInteger (numerator r))) (fromInteger (denominator r))
    recip e1 = AppEE (AppEE (VarEE "__DIV__") (NatEE 1)) e1
    e1 / e2 = AppEE (AppEE (VarEE "__DIV__") e1) e2

evalBaseRing :: Fractional val => EvalEnv val -> BaseRing val -> val
evalBaseRing = go where
    go :: Fractional val => EvalEnv val -> BaseRing val -> val
    go env (PlusEE e1 e2) = go env e1 + go env e2
    go env (MinusEE e1 e2) = go env e1 - go env e2
    go env (MultEE e1 e2) = go env e1 * go env e2
    go env (NatEE n) = fromInteger n
    go env (LitEE v) = v
    go env e = fromJust (tryMatchPrimitive env e /> callWith e [] env)
    tryMatchPrimitive :: Fractional val => EvalEnv val -> BaseRing val -> Maybe val
    tryMatchPrimitive env (VarEE "0") = return 0
    tryMatchPrimitive env (AppEE (VarEE "__ABS__") e1) = return (abs (go env e1))
    tryMatchPrimitive env (AppEE (AppEE (VarEE "__DIV__") e1) e2) = return (go env e1 / go env e2)
    tryMatchPrimitive env _ = Nothing
    callWith :: Fractional val => BaseRing val -> [BaseRing val] -> EvalEnv val -> Maybe val
    callWith (AppEE e1 e2) es env = callWith e1 (e2 : es) env
    callWith (VarEE x) es env = do
        (params, body) <- lookup x env
        let new_env = [ (param, ([], LitEE (go new_env e))) | (param, e) <- zip params es ] ++ env
        if length params == length es
            then return (go new_env body)
            else fail "In `evalBaseRing': parameters.length /= arguments.length"

reduceBaseRing :: ReductionOption -> BaseRing val -> BaseRing val
reduceBaseRing _ = id

bindVarsToVals :: [(VarID, val)] -> EvalEnv val
bindVarsToVals = foldr go [] where
    go :: (VarID, val) -> EvalEnv val -> EvalEnv val
    go (x, v) env = (x, ([], LitEE v)) : env
