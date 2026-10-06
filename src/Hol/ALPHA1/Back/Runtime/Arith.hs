module Hol.ALPHA1.Back.Runtime.Arith where

import Hol.ALPHA1.Back.Base.Constant
import Hol.ALPHA1.Back.Base.TermNode
import Hol.ALPHA1.Back.Base.TermNode.Show
import Hol.ALPHA1.Back.Base.TermNode.Util
import Hol.ALPHA1.Front.Header

data ArithmeticError
    = ArithmeticInstantiation
    | ArithmeticNotEvaluable TermNode
    | ArithmeticNegative Integer
    | ArithmeticNotNatural Integer Integer
    | ArithmeticZeroDivisor
    deriving (Eq)

instance Show ArithmeticError where
    showsPrec _ ArithmeticInstantiation = showString "instantiation_error"
    showsPrec _ (ArithmeticNotEvaluable term) = showString "type_error(evaluable, " . shows term . showString ")"
    showsPrec _ (ArithmeticNegative value) = showString "domain_error(not_less_than_zero, " . shows value . showString ")"
    showsPrec _ (ArithmeticNotNatural numerator denominator) = showString "domain_error(nat, " . shows numerator . showString " / " . shows denominator . showString ")"
    showsPrec _ ArithmeticZeroDivisor = showString "evaluation_error(zero_divisor)"

evalNat :: TermNode -> Either ArithmeticError Integer
evalNat term = case rewrite HNF term of
    NCon (DC (DC_NatL value)) -> natural value
    normalized -> case unfoldlNApp normalized of
        (LVar _, _) -> Left ArithmeticInstantiation
        (NCon (DC DC_Succ), [arg]) -> fmap (+ 1) (evalNat arg)
        (NCon (DC (DC_Arith AO_Positive)), [arg]) -> evalNat arg
        (NCon (DC (DC_Arith AO_Negate)), [arg]) -> evalNat arg >>= natural . negate
        (NCon (DC (DC_Arith operator)), [arg1, arg2]) -> do
            value1 <- evalNat arg1
            value2 <- evalNat arg2
            case operator of
                AO_Add -> return (value1 + value2)
                AO_Subtract -> natural (value1 - value2)
                AO_Multiply -> return (value1 * value2)
                AO_Divide -> do
                    nonzero value2
                    if value1 `mod` value2 == 0 then return (value1 `div` value2) else Left (ArithmeticNotNatural value1 value2)
                AO_Quotient -> nonzero value2 >> return (value1 `quot` value2)
                AO_Div -> nonzero value2 >> return (value1 `div` value2)
                AO_Mod -> nonzero value2 >> return (value1 `mod` value2)
                AO_Rem -> nonzero value2 >> return (value1 `rem` value2)
                _ -> Left (ArithmeticNotEvaluable normalized)
        _ -> Left (ArithmeticNotEvaluable normalized)
    where
        natural :: Integer -> Either ArithmeticError Integer
        natural value = if value >= 0 then return value else Left (ArithmeticNegative value)
        nonzero :: Integer -> Either ArithmeticError ()
        nonzero value = if value == 0 then Left ArithmeticZeroDivisor else return ()

compareNat :: ArithmeticPredicate -> Integer -> Integer -> Bool
compareNat AP_Is = (==)
compareNat AP_Eq = (==)
compareNat AP_Ne = (/=)
compareNat AP_Lt = (<)
compareNat AP_Le = (<=)
compareNat AP_Gt = (>)
compareNat AP_Ge = (>=)
