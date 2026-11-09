module Hol.ALPHA1.Back.Converter.Scheme where

import Hol.ALPHA1.Back.Base.Constant
import Hol.ALPHA1.Back.Base.TermNode
import Hol.ALPHA1.Back.Base.TermNode.Util
import Hol.ALPHA1.Back.Converter.Util
import Hol.ALPHA1.Front.Header
import Hol.ALPHA1.Front.TypeChecker.Util
import Control.Monad
import Control.Monad.Trans.Class
import Control.Monad.Trans.Except
import Control.Monad.Trans.State.Strict
import Data.Functor.Identity
import qualified Data.List as List
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Y.Base

type ExpectedAs = String

type DeBruijnIndicesEnv = [Unique]

type FreeVariableEnv = Map.Map Unique TermNode

convertVar :: FreeVariableEnv -> DeBruijnIndicesEnv -> IVar -> TermNode
convertVar var_name_env env var = case var `List.elemIndex` env of
    Nothing -> maybe (error ("`convertVar\': the variable " ++ shows var " is neither bound nor a query variable.")) id (Map.lookup var var_name_env)
    Just idx -> mkNIdx (idx + 1)

convertType :: FreeVariableEnv -> DeBruijnIndicesEnv -> MonoType Int -> TermNode
convertType var_name_env env (TyMTV mtv) = convertVar var_name_env env mtv
convertType var_name_env env (TyApp typ1 typ2) = mkNApp (convertType var_name_env env typ1) (convertType var_name_env env typ2)
convertType var_name_env env (TyCon (TCon tc _)) = mkNCon tc 
convertType var_name_env env (TyVar _) = error "`convertType\'"

convertCon :: FreeVariableEnv -> DeBruijnIndicesEnv -> DataConstructor -> [MonoType Int] -> TermNode
convertCon var_name_env env con tapps = List.foldl' mkNApp (mkNCon con) (map (convertType var_name_env env) tapps)

convertWithoutChecking :: GenUniqueM m => FreeVariableEnv -> DeBruijnIndicesEnv -> ExpectedAs -> TermExpr (DataConstructor, [MonoType Int]) (SLoc, MonoType Int) -> ExceptT ErrMsg m TermNode
convertWithoutChecking var_name_env = go where
    loop :: DeBruijnIndicesEnv -> TermExpr (DataConstructor, [MonoType Int]) (SLoc, MonoType Int) -> TermNode
    loop env (DCon loc (DC_LO logical_operator, tapps)) = mkNCon logical_operator
    loop env (IVar loc var) = convertVar var_name_env env var
    loop env (DCon loc (data_constructor, tapps)) = convertCon var_name_env env data_constructor tapps
    loop env (IApp loc term1 term2) = mkNApp (loop env term1) (loop env term2)
    loop env (IAbs loc var1 term2) = mkNAbs (loop (var1 : env) term2)
    go :: GenUniqueM m => DeBruijnIndicesEnv -> ExpectedAs -> TermExpr (DataConstructor, [MonoType Int]) (SLoc, MonoType Int) -> ExceptT ErrMsg m TermNode
    go env expected_as term = do
        validateClauseForms expected_as term
        return (loop env (reduceTermExpr term))

validateClauseForms :: GenUniqueM m => ExpectedAs -> TermExpr (DataConstructor, [MonoType Int]) (SLoc, MonoType Int) -> ExceptT ErrMsg m ()
validateClauseForms expected_as = if expected_as == "fact" then clause False else goal where
    reduceHead :: TermExpr dcon annot -> TermExpr dcon annot
    reduceHead (IApp annot term1 term2) = case reduceHead term1 of
        term1'@(IAbs _ _ _) -> reduceHead (reduceTermExpr (IApp annot term1' term2))
        term1' -> IApp annot term1' term2
    reduceHead term = term
    clause :: GenUniqueM m => Bool -> TermExpr (DataConstructor, [MonoType Int]) (SLoc, MonoType Int) -> ExceptT ErrMsg m ()
    clause allow_variables term = case unFoldIApp (reduceHead term) of
        (DCon (loc, _) (DC_LO LO_pi, [typ]), [body]) -> do
            var <- getNewUnique
            clause allow_variables (IApp (loc, mkTyO) body (IVar (loc, typ) var))
        (DCon _ (DC_LO LO_if, _), [conclusion, premise]) -> atom allow_variables conclusion >> goal premise
        _ -> atom allow_variables term
    atom :: GenUniqueM m => Bool -> TermExpr (DataConstructor, [MonoType Int]) (SLoc, MonoType Int) -> ExceptT ErrMsg m ()
    atom allow_variables term = case unFoldIApp (reduceHead term) of
        (DCon _ (DC_LO _, _), _) -> invalid term
        (DCon (loc, _) (DC_Eq, _), _) -> throwE ("*** converting-error[" ++ pprint 0 loc "]:\n  ? the built-in predicate `=\' cannot be given a clause.")
        (DCon _ _, _) -> return ()
        (IVar _ _, _) | allow_variables -> return ()
        _ -> invalid term
    goal :: GenUniqueM m => TermExpr (DataConstructor, [MonoType Int]) (SLoc, MonoType Int) -> ExceptT ErrMsg m ()
    goal term = case unFoldIApp (reduceHead term) of
        (DCon _ (DC_LO LO_imply, _), [antecedent, consequent]) -> clause True antecedent >> goal consequent
        (DCon _ (DC_LO logical_operator, _), [goal1, goal2])
            | logical_operator `elem` [LO_and, LO_or] -> goal goal1 >> goal goal2
        (DCon (loc, _) (DC_LO logical_operator, [typ]), [body])
            | logical_operator `elem` [LO_pi, LO_sigma] -> do
                var <- getNewUnique
                goal (IApp (loc, mkTyO) body (IVar (loc, typ) var))
        (DCon (loc, _) (DC_LO logical_operator, _), _)
            | isGoalOperator logical_operator -> return ()
            | otherwise -> throwE ("*** converting-error[" ++ pprint 0 loc "]:\n  ? `" ++ shows logical_operator "\' cannot occur as a goal.")
        _ -> return ()
    isGoalOperator :: LogicalOperator -> Bool
    isGoalOperator (LO_Arith _) = True
    isGoalOperator logical_operator = logical_operator `elem` [LO_true, LO_fail, LO_cut, LO_debug]
    invalid :: Monad m => TermExpr (DataConstructor, [MonoType Int]) (SLoc, MonoType Int) -> ExceptT ErrMsg m ()
    invalid term = throwE ("*** converting-error[" ++ pprint 0 (fst (getAnnot term)) "]:\n  ? invalid clause head: expected an atomic predicate, optionally preceded by pi or followed by :-.")
