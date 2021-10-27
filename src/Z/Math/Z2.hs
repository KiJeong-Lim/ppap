module Z.Math.Z2 where

import Data.Function

data Z2
    = Z2
        { asBool :: !(Bool)
        }
    deriving ()

instance Num (Z2) where
    x1 + x2 = toZ2 (fromZ2 x1 + fromZ2 x2)
    negate x1 = toZ2 (negate (fromZ2 x1))
    x1 * x2 = toZ2 (fromZ2 x1 * fromZ2 x2)
    abs x1 = toZ2 (abs (fromZ2 x1))
    signum x1 = toZ2 (signum (fromZ2 x1))
    fromInteger = toZ2

instance Eq (Z2) where
    (==) = (==) `on` fromZ2

instance Ord (Z2) where
    compare = compare `on` fromZ2

instance Enum (Z2) where
    toEnum = toZ2 . toEnum
    fromEnum = fromEnum . fromZ2

instance Fractional (Z2) where
    fromRational = error "cannot embed $Q$ into $Z_{2}$..."
    x1 / x2 = divZ2 x1 x2

instance Read (Z2) where
    readsPrec prec ('1' : str) = curry pure (Z2 { asBool = True }) str
    readsPrec prec ('0' : str) = curry pure (Z2 { asBool = False }) str
    readsPrec prec _ = fail ""

instance Show (Z2) where
    showsPrec prec (Z2 { asBool = True }) str = ('1' : str)
    showsPrec prec (Z2 { asBool = False }) str = ('0' : str)

toZ2 :: Integer -> Z2
toZ2 n = Z2 { asBool = n `mod` 2 == 1 }

fromZ2 :: Z2 -> Integer
fromZ2 x = if asBool x then 1 else 0

divZ2 :: Z2 -> Z2 -> Z2
divZ2 x1 x2 = if x2 == 0 then error "Z.Math.Z2.divZ2> divided by 0" else x1
