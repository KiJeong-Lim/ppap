module Z.Math.Temp where

import qualified Data.Map as Map
import Y.Base

type VarID = String

type ReduceOption = String

data ElemExpr val
    = PlusEE (ElemExpr val) (ElemExpr val)
    | MinusEE (ElemExpr val) (ElemExpr val)
    | MultEE (ElemExpr val) (ElemExpr val)
    | DivEE (ElemExpr val) (ElemExpr val)
    | NegEE (ElemExpr val) (ElemExpr val)
    | AbsEE (ElemExpr val)
    | VarEE (VarID)
    | AppEE (ElemExpr val) (ElemExpr val)
    | LitEE (val)
    deriving (Eq, Ord)

instance Num val => Num (ElemExpr val) where
    e1 + e2 = mkPlusEE e1 e2
    e1 - e2 = mkMinusEE e1 e2
    e1 * e2 = mkMultEE e1 e2
    negate e1 = mkMinusEE (mkLitEE 0) e1
    abs e1 = mkAbsEE e1
    signum e1 = mkDivEE e1 (AbsEE e1)
    fromInteger n = mkLitEE (fromInteger n)

instance Show val => Show (ElemExpr val) where
    showsPrec prec = dispatch where
        lowPrecIs :: Int -> ShowS -> ShowS
        lowPrecIs prec' ss = if prec > prec' then strstr "(" . ss . strstr ")" else ss
        dispatch :: Show val => ElemExpr val -> ShowS
        dispatch (PlusEE e1 e2) = lowPrecIs 4 (showsPrec 4 e1 . strstr " + " . showsPrec 5 e2)
        dispatch (MinusEE e1 e2) = lowPrecIs 4 (showsPrec 4 e1 . strstr " - " . showsPrec 5 e2)
        dispatch (MultEE e1 e2) = lowPrecIs 5 (showsPrec 5 e1 . strstr " * " . showsPrec 6 e2)
        dispatch (DivEE e1 e2) = lowPrecIs 5 (showsPrec 5 e1 . strstr " / " . showsPrec 6 e2)
        dispatch (AbsEE e1) = lowPrecIs 0 (strstr "|" . showsPrec 0 e1 . strstr "|")
        dispatch (VarEE var) = lowPrecIs 11 (strstr var)
        dispatch (AppEE e1 e2) = lowPrecIs 10 (showsPrec 10 e1 . strstr " " . showsPrec 11 e2)
        dispatch (LitEE val) = lowPrecIs 11 (showsPrec 11 val)

instance Functor ElemExpr where
    fmap f (PlusEE e1 e2) = PlusEE (fmap f e1) (fmap f e2)
    fmap f (MinusEE e1 e2) = MinusEE (fmap f e1) (fmap f e2)
    fmap f (MultEE e1 e2) = MultEE (fmap f e1) (fmap f e2)
    fmap f (DivEE e1 e2) = DivEE (fmap f e1) (fmap f e2)
    fmap f (AbsEE e1) = AbsEE (fmap f e1)
    fmap f (VarEE var) = VarEE var
    fmap f (AppEE e1 e2) = AppEE (fmap f e1) (fmap f e2)
    fmap f (LitEE val) = LitEE (f val)

mkPlusEE :: Num val => ElemExpr val -> ElemExpr val -> ElemExpr val
mkPlusEE e1 e2 = e1 `seq` e2 `seq` PlusEE e1 e2

mkMinusEE :: Num val => ElemExpr val -> ElemExpr val -> ElemExpr val
mkMinusEE e1 e2 = e1 `seq` e2 `seq` MinusEE e1 e2

mkMultEE :: Num val => ElemExpr val -> ElemExpr val -> ElemExpr val
mkMultEE e1 e2 = e1 `seq` e2 `seq` MultEE e1 e2

mkDivEE :: Num val => ElemExpr val -> ElemExpr val -> ElemExpr val
mkDivEE e1 e2 = e1 `seq` e2 `seq` DivEE e1 e2

mkAbsEE :: Num val => ElemExpr val -> ElemExpr val
mkAbsEE e1 = e1 `seq` AbsEE e1

mkVarEE :: Num val => VarID -> ElemExpr val
mkVarEE = VarEE

mkAppEE :: Num val => ElemExpr val -> ElemExpr val -> ElemExpr val
mkAppEE e1 e2 = e1 `seq` e2 `seq` AppEE e1 e2

mkLitEE :: Num val => val -> ElemExpr val
mkLitEE val = val `seq` LitEE val

evalElemExpr :: Fractional val => Map.Map VarID val -> ElemExpr val -> val
evalElemExpr mapsto (PlusEE e1 e2) = evalElemExpr mapsto e1 + evalElemExpr mapsto e2
evalElemExpr mapsto (MinusEE e1 e2) = evalElemExpr mapsto e1 - evalElemExpr mapsto e2
evalElemExpr mapsto (MultEE e1 e2) = evalElemExpr mapsto e1 * evalElemExpr mapsto e2
evalElemExpr mapsto (DivEE e1 e2) = evalElemExpr mapsto e1 / evalElemExpr mapsto e2
evalElemExpr mapsto (LitEE val) = val
evalElemExpr mapsto (VarEE var) = if var == "__INF__" then 1000000 else mapsto Map.! var

reduceElemExpr :: (Eq val, Fractional val) => ReduceOption -> ElemExpr val -> ElemExpr val
reduceElemExpr = go where
    simplifyLow :: Fractional val => ElemExpr val -> ElemExpr val
    simplifyLow (PlusEE e1 e2)
        | LitEE val1 <- e1
        , LitEE val2 <- e2
        = LitEE (val1 + val2)
        | otherwise
        = mkPlusEE (simplifyLow e1) (simplifyLow e2)
    simplifyLow (MinusEE e1 e2)
        | LitEE val1 <- e1
        , LitEE val2 <- e2
        = LitEE (val1 - val2)
        | otherwise
        = mkMinusEE (simplifyLow e1) (simplifyLow e2)
    simplifyLow (MultEE e1 e2)
        | LitEE val1 <- e1
        , LitEE val2 <- e2
        = LitEE (val1 * val2)
        | otherwise
        = mkMultEE (simplifyLow e1) (simplifyLow e2)
    simplifyLow (DivEE e1 e2)
        | LitEE val1 <- e1
        , LitEE val2 <- e2
        = LitEE (val1 / val2)
        | otherwise
        = mkDivEE (simplifyLow e1) (simplifyLow e2)
    simplifyLow e = e
    lowPlusEE :: (Eq val, Fractional val) => ElemExpr val -> ElemExpr val -> ElemExpr val
    lowPlusEE e1 e2
        | e1 == LitEE 0 = e2
        | e2 == LitEE 0 = e1
        | otherwise = mkPlusEE e1 e2
    lowMinusEE :: (Eq val, Fractional val) => ElemExpr val -> ElemExpr val -> ElemExpr val
    lowMinusEE e1 (MinusEE e2 e3)
        | e2 == LitEE 0 = lowPlusEE e1 e3
    lowMinusEE e1 e2
        | e2 == LitEE 0 = e1
        | e1 == e2 = LitEE 0
        | otherwise = mkMinusEE e1 e2
    lowMultEE :: (Eq val, Fractional val) => ElemExpr val -> ElemExpr val -> ElemExpr val
    lowMultEE e1 e2
        | e1 == LitEE 0 || e2 == LitEE 0 = 0
    lowMultEE (LitEE 1) e = e
    lowMultEE e (LitEE 1) = e
    lowMultEE e1 (MultEE e2 e3) = lowMultEE (lowMultEE e1 e2) e3
    lowMultEE e1 e2 = MultEE e1 e2
    lowDivEE :: (Eq val, Fractional val) => ElemExpr val -> ElemExpr val -> ElemExpr val
    lowDivEE e1 (DivEE e2 e3) = mkDivEE (mkMultEE e1 e3) e2
    lowDivEE e1 e2
        | e1 == e2 = LitEE 1
        | e1 == LitEE 0 = e1
        | e2 == LitEE 1 = e1
        | otherwise = DivEE e1 e2
    lowAbsEE :: (Eq val, Fractional val) => ElemExpr val -> ElemExpr val
    lowAbsEE e1 = e1 `seq` AbsEE e1
    lowVarEE :: (Eq val, Fractional val) => VarID -> ElemExpr val
    lowVarEE = VarEE
    lowAppEE :: (Eq val, Fractional val) => ElemExpr val -> ElemExpr val -> ElemExpr val
    lowAppEE e1 e2 = e1 `seq` e2 `seq` AppEE e1 e2
    lowLitEE :: (Eq val, Fractional val) => val -> ElemExpr val
    lowLitEE val = val `seq` LitEE val
    reduceLow :: (Eq val, Fractional val) => ElemExpr val -> ElemExpr val
    reduceLow (PlusEE e1 e2) = lowPlusEE (reduceLow e1) (reduceLow e2)
    reduceLow (MinusEE e1 e2) = lowMinusEE (reduceLow e1) (reduceLow e2)
    reduceLow (MultEE e1 e2) = lowMultEE (reduceLow e1) (reduceLow e2)
    reduceLow (DivEE e1 e2) = lowDivEE (reduceLow e1) (reduceLow e2)
    reduceLow (AbsEE e1) = lowAbsEE (reduceLow e1)
    reduceLow (VarEE var) = lowVarEE var
    reduceLow (AppEE e1 e2) = lowAppEE (reduceLow e1) (reduceLow e2)
    reduceLow (LitEE val) = lowLitEE val
    go :: (Eq val, Fractional val) => ReduceOption -> ElemExpr val -> ElemExpr val
    go "low" = head . drop 1000 . iterate (simplifyLow . reduceLow)
    go _ = id
