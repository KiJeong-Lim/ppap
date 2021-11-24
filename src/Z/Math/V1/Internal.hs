module Z.Math.V1.Internal where

import Data.Function
import qualified Data.List as List
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Ratio
import Y.Base
import Z.Algo.Function
import Z.Math.Classes
import Z.Text.PC

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
    | DivCE (CoreExpr val) (CoreExpr val)
    deriving (Show)

instance (Num val, Eq val) => Eq (Value val) where
    IntV int1 == IntV int2 = int1 == int2
    LitV val1 == IntV int2 = val1 == fromInteger int2
    IntV int1 == LitV val2 = fromInteger int1 == val2
    LitV val1 == LitV val2 = val1 == val2

castValue :: Value val -> Either Integer val
castValue (IntV n) = Left n
castValue (LitV v) = Right v

reduceCoreToFraction :: (Eq val, Fractional val) => CoreExpr val -> CoreExpr val
reduceCoreToFraction = id
