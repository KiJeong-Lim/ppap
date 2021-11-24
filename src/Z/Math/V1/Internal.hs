module Z.Math.V1.Internal where

import Data.Function
import Data.Functor.Identity
import qualified Data.List as List
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Ratio
import Y.Base
import Z.Algo.Function
import Z.Algo.Sorting (sortByMerging)
import Z.Math.Classes

type IVar = Int

data Value val
    = IntV (Integer)
    | LitV (val)
    deriving (Show)

data CoreExpr val
    = VarCE (IVar)
    | ValCE (Value val)
    | PluCE (CoreExpr val) (CoreExpr val)
    | NegCE (CoreExpr val)
    | MulCE (CoreExpr val) (CoreExpr val)
    | InvCE (CoreExpr val)
    deriving (Eq)

newtype Series
    = Series { unSeries :: [Int] }
    deriving (Show)

instance Eq (Series) where
    (==) = curry (uncurry (==) . pairing) `on` unSeries

instance Ord (Series) where
    compare = curry (uncurry compare . pairing) `on` unSeries

instance (Num val, Eq val) => Eq (Value val) where
    IntV i1 == IntV i2 = i1 == i2
    LitV v1 == IntV i2 = v1 == fromInteger i2
    IntV i1 == LitV v2 = fromInteger i1 == v2
    LitV v1 == LitV v2 = v1 == v2

instance (Num val) => Num (Value val) where
    (+) = lift2Value (+) (+)
    negate = lift1Value negate negate
    (*) = lift2Value (*) (*)
    abs = lift1Value abs abs
    signum = lift1Value signum signum
    fromInteger i = IntV $! i

instance (Fractional val) => Fractional (Value val) where
    fromRational f = LitV $! fromRational f
    (/) = lift2Value div (/)

instance Num (CoreExpr val) where
    e1 + e2 = e1 `seq` e2 `seq` PluCE e1 e2
    negate e1 = e1 `seq` NegCE e1
    e1 * e2 = e1 `seq` e2 `seq` MulCE e1 e2
    signum = const (mkIntCE 1)
    abs = id
    fromInteger = mkIntCE

instance Fractional (CoreExpr val) where
    fromRational f = fromInteger (numerator f) / fromInteger (denominator f)
    e1 / e2 = e1 `seq` e2 `seq` MulCE e1 (InvCE e2)

pairing :: ([Int], [Int]) -> ([Int], [Int])
pairing (xs1, xs2) = (xs1 ++ replicate (max len1 len2 - len1) 0, xs2 ++ replicate (max len1 len2 - len2) 0) where
    len1 :: Int
    len1 = length xs1
    len2 :: Int
    len2 = length xs2

fromValue :: Value val -> Either Integer val
fromValue (IntV i) = Left i
fromValue (LitV v) = Right v

lift1Value :: (Integer -> Integer) -> (val -> val) -> Value val -> Value val
lift1Value op_int op_lit (IntV i1) = IntV $! op_int i1
lift1Value op_int op_lit (LitV v1) = LitV $! op_lit v1

lift2Value :: (Num val) => (Integer -> Integer -> Integer) -> (val -> val -> val) -> Value val -> Value val -> Value val
lift2Value op_int op_lit (IntV i1) (IntV i2) = IntV $! op_int i1 i2
lift2Value op_int op_lit (IntV i1) (LitV v2) = LitV $! op_lit (fromInteger i1) v2
lift2Value op_int op_lit (LitV v1) (IntV i2) = LitV $! op_lit v1 (fromInteger i2)
lift2Value op_int op_lit (LitV v1) (LitV v2) = LitV $! op_lit v1 v2

toLitV :: (Num val) => Value val -> Value val
toLitV (IntV i) = LitV $! fromInteger i
toLitV v = v

consfst :: a -> ([a], b) -> ([a], b)
consfst x (xs, y) = (x : xs, y)

conssnd :: b -> (a, [b]) -> (a, [b])
conssnd y (x, ys) = (x, y : ys)

deleteone :: (a -> Bool) -> [a] -> [a]
deleteone kill_cond [] = []
deleteone kill_cond (x : xs) = if kill_cond x then xs else x : deleteone kill_cond xs

attrition :: (a -> a -> Bool) -> [a] -> [a] -> ([a], [a])
attrition equiv [] ys = ([], ys)
attrition equiv (x : xs) ys = if all (\y -> not (x `equiv` y)) ys then consfst x (attrition equiv xs ys) else attrition equiv xs (deleteone (\y -> x `equiv` y) ys)

mkVarCE :: IVar -> CoreExpr val
mkVarCE = VarCE

mkValCE :: Value val -> CoreExpr val
mkValCE v = v `seq` ValCE v

mkIntCE :: Integer -> CoreExpr val
mkIntCE i = mkValCE (i `seq` IntV i)

mkLitCE :: (Eq val, Num val) => val -> CoreExpr val
mkLitCE v = if v == 0 then mkIntCE 0 else mkValCE (LitV v)

mkPluCE :: (Eq val, Num val) => CoreExpr val -> CoreExpr val -> CoreExpr val
mkPluCE (ValCE v1) (ValCE v2) = mkValCE (v1 + v2)
mkPluCE e1 (ValCE v2) = mkPluCEaux1 e1 v2
mkPluCE e1 (PluCE e2 e3) = mkPluCE (mkPluCE e1 e2) e3
mkPluCE e1 e2 = e1 + e2

mkPluCEaux1 :: (Eq val, Num val) => CoreExpr val -> Value val -> CoreExpr val
mkPluCEaux1 e1 v2
    | v2 == 0 = e1
    | otherwise = mkPluCE (mkValCE v2) e1

mkNegCE :: (Eq val, Num val) => CoreExpr val -> CoreExpr val
mkNegCE (ValCE v) = mkValCE (negate v)
mkNegCE (MulCE e1 e2) = mkMulCE (mkNegCE e1) e2
mkNegCE e1 = negate e1

mkMulCE :: (Eq val, Num val) => CoreExpr val -> CoreExpr val -> CoreExpr val
mkMulCE (ValCE v1) (ValCE v2) = mkValCE (v1 * v2)
mkMulCE e1 (ValCE v2) = mkMulCEaux1 e1 v2
mkMulCE e1 (NegCE e2) = mkNegCE (mkMulCE e1 e2)
mkMulCE e1 (MulCE e2 e3) = mkMulCE (mkMulCE e1 e2) e3
mkMulCE e1 e2 = e1 * e2

mkMulCEaux1 :: (Eq val, Num val) => CoreExpr val -> Value val -> CoreExpr val
mkMulCEaux1 e1 v2
    | signum v2 == negate 1 = mkNegCE (mkMulCEaux1 e1 (abs v2))
    | v2 == 0 = mkLitCE 0
    | v2 == 1 = e1
    | otherwise = mkMulCE (mkValCE v2) e1

mkDivCE :: (Eq val, Num val) => CoreExpr val -> CoreExpr val -> CoreExpr val
mkDivCE e1 e2 = mkMulCE e1 (recip e2)

mkInvCE :: (Eq val, Fractional val) => CoreExpr val -> CoreExpr val
mkInvCE (ValCE v) = either (mkLitCE . fromRational . (%) 1) (mkLitCE . recip) (fromValue v)
mkInvCE e = InvCE e

fromValCE :: CoreExpr val -> Maybe (Value val)
fromValCE (ValCE v) = Just v
fromValCE _ = Nothing

prod :: (Eq val, Num val) => [CoreExpr val] -> CoreExpr val
prod = foldr mkMulCE (mkIntCE 1)

unprod :: CoreExpr val -> [CoreExpr val]
unprod (MulCE e1 e2) = unprod e1 ++ unprod e2
unprod e = pure e

coprod :: (Eq val, Num val) => [CoreExpr val] -> CoreExpr val
coprod = foldr mkPluCE (mkIntCE 0)

uncoprod :: CoreExpr val -> [CoreExpr val]
uncoprod (PluCE e1 e2) = uncoprod e1 ++ uncoprod e2
uncoprod e = pure e

lt :: CoreExpr val -> CoreExpr val -> Bool
lt (VarCE x) (VarCE x') = x < x'
lt (VarCE x) _ = True
lt _ (VarCE x') = False
lt (NegCE e1) (NegCE e1') = e1 `lt` e1'
lt (NegCE e1) _ = True
lt _ (NegCE e1') = False
lt (MulCE e1 e2) (MulCE e1' e2') = e1 `lt` e1' || (e1 `eq` e1' && e2 `lt` e2')
lt (MulCE e1 e2) _ = True
lt _ (MulCE e1' e2') = False
lt (PluCE e1 e2) (PluCE e1' e2') = e1 `lt` e1' || (e1 `eq` e1' && e2 `lt` e2')
lt (PluCE e1 e2) _ = True
lt _ (PluCE e1' e2') = False
lt (InvCE e1) (InvCE e1') = e1 `lt` e1'
lt (InvCE e1) _ = True
lt _ (InvCE e1') = False
lt _ _ = False

eq :: CoreExpr val -> CoreExpr val -> Bool
eq (VarCE v) (VarCE v') = v == v'
eq (NegCE e1) (NegCE e1') = e1 `eq` e1'
eq (MulCE e1 e2) (MulCE e1' e2') = e1 `eq` e1' && e2 `eq` e2'
eq (PluCE e1 e2) (PluCE e1' e2') = e1 `eq` e1' && e2 `eq` e2'
eq (InvCE e1) (InvCE e1') = e1' `eq` e1'
eq (ValCE v) (ValCE v') = True
eq _ _ = False

refine :: [CoreExpr val] -> [CoreExpr val]
refine = sortByMerging (\e1 -> \e2 -> e1 `lt` e2 || e1 `eq` e2)

normalize :: (Eq val, Fractional val) => CoreExpr val -> CoreExpr val
normalize = initphase where
    initphase :: (Eq val, Fractional val) => CoreExpr val -> CoreExpr val
    initphase (PluCE e1 e2) = plusphase [] [] 0 [e1, e2] []
    initphase (NegCE e1) = plusphase [] [] 0 [] [e1]
    initphase (MulCE e1 e2) = multphase [] [] 1 [e1, e2] []
    initphase (InvCE e1) = multphase [] [] 1 [] [e1]
    initphase e = e
    multphase :: (Eq val, Fractional val) => [CoreExpr val] -> [CoreExpr val] -> Value val -> [CoreExpr val] -> [CoreExpr val] -> CoreExpr val
    multphase nums dens val [] [] = multphase1 val nums dens
    multphase nums dens val (e : es1) es2 = multphase2 nums dens val es1 (normalize e) es2
    multphase nums dens val es1 (e : es2) = multphase3 nums dens val es1 (normalize e) es2
    multphase1 :: (Eq val, Fractional val) => Value val -> [CoreExpr val] -> [CoreExpr val] -> CoreExpr val
    multphase1 val nums dens
        | signum val == negate 1 = mkNegCE (multphase1 (abs val) nums dens) 
        | val == 0 = 0
        | val == 1 = multphaselast (refine nums) (refine dens)
        | otherwise = mkValCE val * multphaselast (refine nums) (refine dens)
    multphase2 :: (Eq val, Fractional val) => [CoreExpr val] -> [CoreExpr val] -> Value val -> [CoreExpr val] -> CoreExpr val -> [CoreExpr val] -> CoreExpr val
    multphase2 nums dens val es1 (ValCE val') es2 = multphase nums dens (val * val') es1 es2
    multphase2 nums dens val es1 (MulCE e1 e2) es2 = multphase nums dens val (e1 : e2 : es1) es2
    multphase2 nums dens val es1 (NegCE e1) es2 = multphase nums dens (negate val) (e1 : es1) es2
    multphase2 nums dens val es1 (InvCE e1) es2 = multphase nums dens val es1 (e1 : es2)
    multphase2 nums dens val es1 e es2 = multphase (e : nums) dens val es1 es2
    multphase3 :: (Eq val, Fractional val) => [CoreExpr val] -> [CoreExpr val] -> Value val -> [CoreExpr val] -> CoreExpr val -> [CoreExpr val] -> CoreExpr val
    multphase3 nums dens val es1 (ValCE val') es2 = multphase nums dens (toLitV val / toLitV val') es1 es2
    multphase3 nums dens val es1 (MulCE e1 e2) es2 = multphase nums dens val es1 (e1 : e2 : es2)
    multphase3 nums dens val es1 (NegCE e1) es2 = multphase nums dens (negate val) es1 (e1 : es2)
    multphase3 nums dens val es1 (InvCE e1) es2 = multphase nums dens val (e1 : es1) es2
    multphase3 nums dens val es1 e es2 = multphase nums (e : dens) val es1 es2
    multphaselast :: (Eq val, Fractional val) => [CoreExpr val] -> [CoreExpr val] -> CoreExpr val
    multphaselast nums dens = uncurry endmultphase (attrition (==) nums dens)
    endmultphase :: (Eq val, Fractional val) => [CoreExpr val] -> [CoreExpr val] -> CoreExpr val
    endmultphase [] [] = 1
    endmultphase [] (e2 : es2) = mkInvCE (List.foldl' (*) e2 es2)
    endmultphase (e1 : es1) [] = List.foldl' (*) e1 es1
    endmultphase (e1 : es1) (e2 : es2) = List.foldl' (*) e1 es1 / List.foldl' (*) e2 es2
    plusphase :: (Eq val, Fractional val) => [CoreExpr val] -> [CoreExpr val] -> Value val -> [CoreExpr val] -> [CoreExpr val] -> CoreExpr val
    plusphase poss negs val [] [] = plusphase1 val poss negs
    plusphase poss negs val (e : es1) es2 = plusphase2 poss negs val es1 (normalize e) es2
    plusphase poss negs val es1 (e : es2) = plusphase3 poss negs val es1 (normalize e) es2
    plusphase1 :: (Eq val, Fractional val) => Value val -> [CoreExpr val] -> [CoreExpr val] -> CoreExpr val
    plusphase1 val poss negs
        | signum val == negate 1 = plusphaselast (refine poss) (refine (mkValCE (abs val) : negs))
        | val == 0 = plusphaselast (refine poss) (refine negs)
        | otherwise = plusphaselast (refine (mkValCE val : poss)) negs
    plusphase2 :: (Eq val, Fractional val) => [CoreExpr val] -> [CoreExpr val] -> Value val -> [CoreExpr val] -> CoreExpr val -> [CoreExpr val] -> CoreExpr val
    plusphase2 poss negs val es1 (ValCE val') es2 = plusphase poss negs (val + val') es1 es2
    plusphase2 poss negs val es1 (PluCE e1 e2) es2 = plusphase poss negs val (e1 : e2 : es1) es2
    plusphase2 poss negs val es1 (NegCE e1) es2 = plusphase poss negs val es1 (e1 : es2)
    plusphase2 poss negs val es1 e es2 = plusphase (e : poss) negs val es1 es2
    plusphase3 :: (Eq val, Fractional val) => [CoreExpr val] -> [CoreExpr val] -> Value val -> [CoreExpr val] -> CoreExpr val -> [CoreExpr val] -> CoreExpr val
    plusphase3 poss negs val es1 (ValCE val') es2 = plusphase poss negs (val - val') es1 es2
    plusphase3 poss negs val es1 (PluCE e1 e2) es2 = plusphase poss negs val es1 (e1 : e2 : es2)
    plusphase3 poss negs val es1 (NegCE e1) es2 = plusphase poss negs val (e1 : es1) es2
    plusphase3 poss negs val es1 e es2 = plusphase poss (e : negs) val es1 es2
    plusphaselast :: (Eq val, Fractional val) => [CoreExpr val] -> [CoreExpr val] -> CoreExpr val
    plusphaselast poss negs = uncurry endplusphase (attrition (==) poss negs)
    endplusphase :: (Eq val, Fractional val) => [CoreExpr val] -> [CoreExpr val] -> CoreExpr val
    endplusphase [] [] = 0
    endplusphase [] (e2 : es2) = mkNegCE (List.foldl' (+) e2 es2)
    endplusphase (e1 : es1) [] = List.foldl' (+) e1 es1
    endplusphase (e1 : es1) (e2 : es2) = List.foldl' (+) e1 es1 - List.foldl' (+) e2 es2

factoronce :: (Eq val, Fractional val) => CoreExpr val -> CoreExpr val -> CoreExpr val
factoronce = curry (normalize . uncurry (go 1 `on` unprod . normalize)) where
    go :: (Eq val, Fractional val) => CoreExpr val -> [CoreExpr val] -> [CoreExpr val] -> CoreExpr val
    go e [] [] = mkPluCE e 1
    go e [] (e2 : es2) = mkPluCE e (List.foldl' mkMulCE e2 es2)
    go e (e1 : es1) es2 = maybe (go (e * e1) es1 es2) (uncurry $ \e1' -> \es2' -> e1' * go e es1 es2') (loop1 e1 es2)
    loop1 :: (Eq val, Fractional val) => CoreExpr val -> [CoreExpr val] -> Maybe (CoreExpr val, [CoreExpr val])
    loop1 e1 [] = Nothing
    loop1 (ValCE v1) (ValCE v2 : es) = return (mkValCE v1, mkValCE (toLitV v2 / toLitV v1) : es)
    loop1 e1 (e2 : es)
        | e1 == e2 = return (e1, es)
        | otherwise = do
            (e1', es') <- loop1 e1 es
            return (e1', e2 : es')

reduceCoreToFraction :: (Eq val, Fractional val) => CoreExpr val -> CoreExpr val
reduceCoreToFraction = uncurry unfractionalize . fractionalize where
    fractionalize :: (Eq val, Fractional val) => CoreExpr val -> (CoreExpr val, CoreExpr val)
    fractionalize (PluCE e1 e2) = fracplu (fractionalize e1) (fractionalize e2)
    fractionalize (NegCE e1) = fracneg (fractionalize e1)
    fractionalize (MulCE e1 e2) = fracmul (fractionalize e1) (fractionalize e2)
    fractionalize (InvCE e1) = fracinv (fractionalize e1)
    fractionalize (ValCE v) = fracval v
    fractionalize (VarCE x) = fracvar x
    fracplu :: (Eq val, Fractional val) => (CoreExpr val, CoreExpr val) -> (CoreExpr val, CoreExpr val) -> (CoreExpr val, CoreExpr val)
    fracplu (num1, den1) (num2, den2) = (factoronce (mkMulCE num1 den2) (mkMulCE num2 den1), mkMulCE den1 den2)
    fracneg :: (Eq val, Num val) => (CoreExpr val, CoreExpr val) -> (CoreExpr val, CoreExpr val)
    fracneg (num1, den1) = (mkNegCE num1, den1)
    fracmul :: (Eq val, Num val) => (CoreExpr val, CoreExpr val) -> (CoreExpr val, CoreExpr val) -> (CoreExpr val, CoreExpr val)
    fracmul (num1, den1) (num2, den2) = (mkMulCE num1 num2, mkMulCE den1 den2)
    fracinv :: (Eq val, Num val) => (CoreExpr val, CoreExpr val) -> (CoreExpr val, CoreExpr val)
    fracinv (num1, den1) = (den1, num1)
    fracval :: Value val -> (CoreExpr val, CoreExpr val)
    fracval v = (ValCE v, 1)
    fracvar :: IVar -> (CoreExpr val, CoreExpr val)
    fracvar x = (VarCE x, 1)
    unfractionalize :: (Eq val, Fractional val) => CoreExpr val -> CoreExpr val -> CoreExpr val
    unfractionalize = curry (normalize . uncurry (mkDivCE `on` prod) . uncurry (attrition (==))) `on` unprod . normalize

testunit1 :: CoreExpr Double
testunit1 = 3 * (1 + 3 * VarCE 1 + VarCE 2) / negate (VarCE 2 * 2 + 2 * VarCE 1 * 3 + 2)
