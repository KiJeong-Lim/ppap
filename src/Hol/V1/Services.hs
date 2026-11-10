module Hol.V1.Services where

import Calc.Presburger.Internal (MyPresburgerFormulaRep, MyVar)
import Control.Monad
import Control.Monad.IO.Class
import Control.Monad.Trans.Except
import Data.IORef
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Hol.BETA.Arith
import Hol.BETA.Constant
import Hol.BETA.Header
import Hol.BETA.HOPU
import Hol.BETA.Runtime
import Hol.BETA.TermNode

-- Search, scope allocation and higher-order unification remain in the C VM.
-- Services return bindings and obligations for the VM to install atomically.
data ServiceRequest
    = Settle
    | Evaluate TermNode TermNode
    | Compare Constant [TermNode]
    | EqualityDefinitions [TermNode]
    | EqualityDecision [TermNode]
    | Presburger MyPresburgerFormulaRep (Map.Map MyVar TermNode)
    | AssumePremises TermNode
    | Print [TermNode]
    | Read [TermNode]
    | Debug TermNode
    deriving ()

data ServiceResult
    = ServiceFailure
    | ServiceContinue Context ArithStore
    | ServiceUnify Context ArithStore TermNode TermNode
    | ServiceUndecided Context ArithStore
    | ServiceEquality (Maybe Bool) Context ArithStore
    | ServiceReject
    deriving ()

runService :: UniqueM m => RuntimeEnv -> ArithStore -> Context -> ServiceRequest -> ExceptT KernelErr m ServiceResult
runService env premises ctx request = case request of
    Settle -> return (settle premises ctx)
    Evaluate lhs rhs -> return (evaluateService premises ctx lhs rhs)
    Compare predicate args -> comparisonService env premises ctx predicate args
    EqualityDefinitions args -> return $ case args of
        [_, lhs, rhs]
            | equalityUsesArithmetic args ->
                maybe ServiceFailure (\defined -> ServiceContinue defined premises) (addDefinitionConstraints [bound lhs, bound rhs] ctx)
        _ -> ServiceContinue ctx premises
    EqualityDecision args -> return $ case args of
        [_, lhs, rhs]
            | equalityUsesArithmetic args -> case arithmeticEquality (bound lhs) (bound rhs) of
                ArithEqTrue -> ServiceEquality (Just True) ctx premises
                ArithEqFalse -> ServiceEquality (Just False) ctx premises
                ArithEqUnknown -> ServiceEquality Nothing ctx premises
        _ -> ServiceEquality Nothing ctx premises
    Presburger rep freeOf -> return $ case runPresburger rep freeOf premises ctx [] [] of
        (next, _) : _ -> ServiceContinue next premises
        [] -> ServiceFailure
    AssumePremises fact -> do
        additions <- instantiateArithPremises fact
        return (ServiceContinue ctx (appendArithStore premises additions))
    Print args -> case primitiveArg args of
        Nothing -> throwE (BadGoalGiven (foldlNApp (mkNCon (DC_Named "print")) args))
        Just arg -> do
            liftIO (_PrintPrimitive env ctx (bound arg))
            return (ServiceContinue ctx premises)
    Read args -> case primitiveArg args of
        Nothing -> throwE (BadGoalGiven (foldlNApp (mkNCon (DC_Named "read")) args))
        Just arg -> do
            value <- liftIO (_ReadPrimitive env ctx arg)
            return $ case value of
                Nothing -> ServiceFailure
                Just term -> case rewrite NF (bound arg) of
                    LVar variable
                        | admissible variable term -> settle premises (zonkLVar (VarBinding (Map.singleton variable term)) ctx)
                    current
                        | current == rewrite NF term -> ServiceContinue ctx premises
                    _ -> ServiceFailure
    Debug label -> do
        liftIO (writeIORef (_debuggindModeOn ctx) True)
        liftIO (putStrLn ("*** debugger called with " ++ shows label ""))
        return (ServiceContinue ctx premises)
    where
        bound = bindVars (_TotalVarBinding ctx)
        admissible variable term = variable `Set.notMember` getLVars term
            && null badConstants && null badVariables
            && primitiveBindingTypeOkayWithKinds (_ProgramKindEnv env) (_CurrentLabeling ctx) variable term
            where
                (badConstants, badVariables) = scopeEscaping (_CurrentLabeling ctx) (lookupLabel variable (_CurrentLabeling ctx)) variable term

primitiveArg :: [TermNode] -> Maybe TermNode
primitiveArg [arg] = Just arg
primitiveArg [_, arg] = Just arg
primitiveArg _ = Nothing

-- Every other equality is decided by the native search alone: its two
-- service replies do not depend on the context.
equalityUsesArithmetic :: [TermNode] -> Bool
equalityUsesArithmetic args = case args of
    [typ, lhs, rhs] -> natType typ || mentionsArithmetic lhs || mentionsArithmetic rhs
    _ -> False

natType :: TermNode -> Bool
natType typ = case rewrite NF typ of
    NCon (TC (TC_Named "nat")) _ -> True
    _ -> False

settle :: ArithStore -> Context -> ServiceResult
settle premises ctx = case settleEvaluationConstraints ctx [] of
    Nothing -> ServiceFailure
    Just (next, _) -> ServiceContinue next premises

evaluateService :: ArithStore -> Context -> TermNode -> TermNode -> ServiceResult
evaluateService premises ctx lhs rhs
    | Left "ill" == rhsValue = ServiceFailure
    | LVar variable <- lhs'
    , Right value <- rhsValue = bindResult ctx variable (mkNCon (DC_NatL value))
    | Right value <- rhsValue
    , Right expected <- evaluateA lhs' = if expected == value then ServiceContinue ctx premises else ServiceFailure
    | LVar variable <- lhs'
    , Just result <- simplifyArithmetic rhs'
    , admissible variable result = case addDefinitionConstraints [rhs'] ctx of
        Nothing -> ServiceFailure
        Just defined -> bindResult defined variable result
    | ArithEqTrue <- arithmeticEquality lhs' rhs' =
        maybe ServiceFailure (\defined -> ServiceContinue defined premises) (addDefinitionConstraints [lhs', rhs'] ctx)
    | ArithEqFalse <- arithmeticEquality lhs' rhs' = ServiceFailure
    | not arithmeticMode = ServiceUnify ctx premises lhs' rhs'
    | otherwise = settle premises (ctx { _LeftConstraints = EvalutionConstraint lhs' rhs' : _LeftConstraints ctx })
    where
        lhs' = rewrite NF (bindVars (_TotalVarBinding ctx) lhs)
        rhs' = rewrite NF (bindVars (_TotalVarBinding ctx) rhs)
        rhsValue = evaluateA rhs'
        arithmeticMode = isNat lhs' || isNat rhs' || mentionsArithmetic lhs' || mentionsArithmetic rhs'
        isNat (NCon (DC (DC_NatL _)) _) = True
        isNat term = typeOfTerm (_CurrentLabeling ctx) [] term == Just mkTyNat
        bindResult active variable value = settle premises (zonkLVar (VarBinding (Map.singleton variable value)) active)
        admissible variable term = variable `Set.notMember` getLVars term && null badConstants && null badVariables where
            (badConstants, badVariables) = scopeEscaping (_CurrentLabeling ctx) (lookupLabel variable (_CurrentLabeling ctx)) variable term

comparisonService :: Monad m => RuntimeEnv -> ArithStore -> Context -> Constant -> [TermNode] -> ExceptT KernelErr m ServiceResult
comparisonService env premises ctx predicate args = case (predicate, args) of
    (DC DC_ge, [_, _]) -> compareWith (>=)
    (DC DC_gt, [_, _]) -> compareWith (>)
    (DC DC_le, [_, _]) -> compareWith (<=)
    (DC DC_lt, [_, _]) -> compareWith (<)
    _ -> throwE (BadGoalGiven (foldlNApp (mkNCon predicate) args))
    where
        boundArgs = map (rewrite NF . bindVars (_TotalVarBinding ctx)) args
        candidate = arithmeticConstraintCandidate (_QueryCallId env) (_ContextThreadId ctx) predicate args boundArgs
        compareWith operator = case addDefinitionConstraints boundArgs ctx of
            Nothing -> return ServiceFailure
            Just defined
                | Just okay <- groundComparison premises (groundResult operator) -> return (if okay then ServiceContinue defined premises else ServiceFailure)
            Just defined -> case liftConstraint candidate of
                Nothing -> case groundResult operator of
                    Right okay -> return (if okay then ServiceContinue defined premises else ServiceFailure)
                    Left "ill" -> return ServiceFailure
                    _ -> throwE (UnsupportedArithmeticConstraint candidate)
                Just lifted
                    | presburgerEntails (arithAssumptions premises defined) (_liftedFormula lifted, _freeOfLifted lifted) -> return (ServiceContinue defined premises)
                    | Right False <- groundResult operator
                    , nullArithStore premises -> return ServiceFailure
                    | Left "ill" <- groundResult operator -> return ServiceFailure
                    | not (storeSatisfiable (retained defined)) -> return ServiceFailure
                    | otherwise -> return (ServiceContinue (retained defined) premises)
        groundResult operator = case boundArgs of
            [left, right] -> liftM2 operator (evaluateA left) (evaluateA right)
            _ -> Left "non"
        retained defined = defined { _LeftConstraints = ArithmeticConstraint premises candidate : _LeftConstraints defined }
