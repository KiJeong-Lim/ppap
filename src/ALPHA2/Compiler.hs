module ALPHA2.Compiler where

import ALPHA2.Header
import ALPHA2.TermNode
import Control.Monad.Trans.Class
import Control.Monad.Trans.Except
import Control.Monad.Trans.State.Strict
import qualified Data.List as List
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Z.Utils

type ExpectedAs = String

type DeBruijnIndicesEnv = [Unique]

type FreeVariableEnv = Map.Map Unique TermNode

convertVar :: FreeVariableEnv -> DeBruijnIndicesEnv -> IVar -> TermNode
convertVar var_name_env env var = case var `List.elemIndex` env of
    Nothing -> var_name_env Map.! var
    Just idx -> mkNIdx idx

convertType :: FreeVariableEnv -> DeBruijnIndicesEnv -> MonoType Int -> TermNode
convertType var_name_env env (TyMTV mtv) = convertVar var_name_env env mtv
convertType var_name_env env (TyApp typ1 typ2) = mkNApp (convertType var_name_env env typ1) (convertType var_name_env env typ2)
convertType var_name_env env (TyCon (TCon tc _)) = mkNCon tc
convertType var_name_env env (TyVar _) = error "`convertType\'"

convertCon :: FreeVariableEnv -> DeBruijnIndicesEnv -> DataConstructor -> [MonoType Int] -> TermNode
convertCon var_name_env env con tapps = List.foldl' mkNApp (mkNCon con) (map (convertType var_name_env env) tapps)

convertWithoutChecking :: MonadUnique m => FreeVariableEnv -> DeBruijnIndicesEnv -> TermExpr (DataConstructor, [MonoType Int]) (SLoc, MonoType Int) -> ExceptT ErrMsg m TermNode
convertWithoutChecking var_name_env = go where
    loop :: DeBruijnIndicesEnv -> TermExpr (DataConstructor, [MonoType Int]) (SLoc, MonoType Int) -> TermNode
    loop env (Con loc (DC_LO logical_operator, tapps)) = mkNCon logical_operator
    loop env (Var loc var) = convertVar var_name_env env var
    loop env (Con loc (data_constructor, tapps)) = convertCon var_name_env env data_constructor tapps
    loop env (App loc term1 term2) = mkNApp (loop env term1) (loop env term2)
    loop env (Lam loc var1 term2) = mkNLam (loop (var1 : env) term2)
    go :: MonadUnique m => DeBruijnIndicesEnv -> TermExpr (DataConstructor, [MonoType Int]) (SLoc, MonoType Int) -> ExceptT ErrMsg m TermNode
    go env = return . loop env . reduceTermExpr

convertProgram :: MonadUnique m => Map.Map MetaTVar SmallId -> Map.Map IVar (MonoType Int) -> TermExpr (DataConstructor, [MonoType Int]) (SLoc, MonoType Int) -> ExceptT ErrMsg m TermNode
convertProgram used_mtvs assumptions = fmap makeUniversalClosure . convertWithoutChecking Map.empty initialEnv where
    initialEnv :: DeBruijnIndicesEnv
    initialEnv = Set.toList (Map.keysSet assumptions `Set.union` Map.keysSet used_mtvs)
    makeUniversalClosure :: TermNode -> TermNode
    makeUniversalClosure = flip (foldr (\_ -> \term -> (mkNApp (mkNCon LO_ty_pi)) (mkNLam term))) [1, 2 .. Map.size used_mtvs] . flip (foldr (\_ -> \term -> mkNApp (mkNCon LO_pi) (mkNLam term))) [1, 2 .. Map.size assumptions]

convertQuery :: MonadUnique m => Map.Map MetaTVar SmallId -> Map.Map IVar (MonoType Int) -> FreeVariableEnv -> TermExpr (DataConstructor, [MonoType Int]) (SLoc, MonoType Int) -> ExceptT ErrMsg m TermNode
convertQuery used_mtvs assumptions var_name_env query
    | Map.null used_mtvs = convertWithoutChecking var_name_env [] query
    | otherwise = do
        extra_env <- sequence
            [ do
                uni <- getUnique
                return (mtv, LVar (LV_ty_var uni))
            | (mtv, small_id) <- Map.toDescList used_mtvs
            ]
        convertWithoutChecking (foldr (uncurry Map.insert) var_name_env extra_env) [] query

viewLam :: TermExpr dcon annot -> ([IVar], TermExpr dcon annot)
viewLam = go [] where
    go :: [IVar] -> TermExpr dcon annot -> ([IVar], TermExpr dcon annot)
    go vars (Lam annot var term) = go (var : vars) term
    go vars term = (vars, term)

unFoldApp :: TermExpr dcon annot -> (TermExpr dcon annot, [TermExpr dcon annot])
unFoldApp = flip go [] where
    go :: TermExpr dcon annot -> [TermExpr dcon annot] -> (TermExpr dcon annot, [TermExpr dcon annot])
    go (App annot term1 term2) terms = go term1 (term2 : terms)
    go term terms = (term, terms)

isPredicate :: MonoType Int -> Bool
isPredicate (TyCon (TCon (TC_Named "o") _)) = True
isPredicate (TyApp (TyApp (TyCon (TCon TC_Arrow _)) typ1) typ2) = isPredicate typ2
isPredicate _ = False

reduceTermExpr :: TermExpr dcon annot -> TermExpr dcon annot
reduceTermExpr = go Map.empty where
    go :: Map.Map IVar (TermExpr tapp annot) -> TermExpr tapp annot -> TermExpr tapp annot
    go mapsto (App annot1 (Lam annot2 var term1) term2)
        = go mapsto (go (Map.singleton var term2) term1)
    go mapsto (Var annot var)
        = case Map.lookup var mapsto of
            Nothing -> Var annot var
            Just term -> term
    go mapsto (Con annot con)
        = Con annot con
    go mapsto (App annot term1 term2)
        = App annot (go mapsto term1) (go mapsto term2)
    go mapsto (Lam annot var term)
        = Lam annot var (go mapsto term)
