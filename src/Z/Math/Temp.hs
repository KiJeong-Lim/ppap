module Z.Math.Temp where

import qualified Data.Map.Strict as Map
import GHC.Real
import Y.Base

type VarID = String

type EvalEnv val = [(VarID, ([VarID], val))]

type ReductionOption = String

data BaseRing val
    = PlusEE (BaseRing val) (BaseRing val)
    | MinusEE (BaseRing val) (BaseRing val)
    | MultEE (BaseRing val) (BaseRing val)
    | VarEE (VarID)
    | AppEE (BaseRing val) (BaseRing val)
    | NatEE (Integer)
    | LitEE (val)
    deriving ()

instance Eq val => Eq (BaseRing val) where
    e1 == e2 = undefined

instance Ord val => Ord (BaseRing val) where
    e1 <= e2 = undefined

instance Show val => Show (BaseRing val) where
    showsPrec prec = dispatch where
        myPrecIs :: Int -> ShowS -> ShowS
        myPrecIs prec' ss = if prec > prec' then strstr "(" . ss . strstr ")" else ss
        dispatch :: Show val => BaseRing val -> ShowS
        dispatch (PlusEE e1 e2) = myPrecIs 4 (showsPrec 4 e1 . strstr " + " . showsPrec 5 e2)
        dispatch (MinusEE e1 e2) = myPrecIs 4 (showsPrec 4 e1 . strstr " - " . showsPrec 5 e2)
        dispatch (MultEE e1 e2) = myPrecIs 5 (showsPrec 5 e1 . strstr " * " . showsPrec 6 e2)
        dispatch (VarEE var) = myPrecIs 11 (strstr var)
        dispatch (AppEE e1 e2) = undefined
        dispatch (NatEE n) = myPrecIs 11 (showsPrec 11 n)
        dispatch (LitEE val) = myPrecIs 11 (showsPrec 11 val)

instance Functor BaseRing where
    fmap f (PlusEE e1 e2) = PlusEE (fmap f e1) (fmap f e2)
    fmap f (MinusEE e1 e2) = MinusEE (fmap f e1) (fmap f e2)
    fmap f (MultEE e1 e2) = MultEE (fmap f e1) (fmap f e2)
    fmap f (VarEE var) = VarEE var
    fmap f (AppEE e1 e2) = AppEE (fmap f e1) (fmap f e2)
    fmap f (NatEE n) = NatEE n
    fmap f (LitEE val) = LitEE (f val)

instance Num val => Num (BaseRing val) where
    e1 + e2 = undefined
    e1 - e2 = undefined
    e1 * e2 = undefined
    negate e1 = undefined
    abs e1 = undefined
    signum e1 = undefined
    fromInteger n = undefined

instance Fractional val => Fractional (BaseRing val) where
    fromRational r = undefined
    recip e1 = undefined
    e1 / e2 = undefined

evalBaseRing :: Fractional val => EvalEnv val -> BaseRing val -> val
evalBaseRing = undefined

reduceBaseRing :: (Eq val, Num val) => ReductionOption -> BaseRing val -> BaseRing val
reduceBaseRing _ = id

bindVarTo :: Fractional val => VarID -> BaseRing val -> EvalEnv val -> EvalEnv val
bindVarTo x e env = (x, ([], evalBaseRing env e)) : env

bindVarsToVals :: [(VarID, val)] -> EvalEnv val
bindVarsToVals = foldr go [] where
    go :: (VarID, val) -> EvalEnv val -> EvalEnv val
    go (x, v) env = (x, ([], v)) : env
