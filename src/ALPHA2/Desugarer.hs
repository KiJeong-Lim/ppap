module ALPHA2.Desugarer where

import ALPHA2.Header
import ALPHA2.PlanHolLexer
import Control.Monad.Trans.Class
import Control.Monad.Trans.Except
import Control.Monad.Trans.State.Strict
import qualified Data.List as List
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Z.Utils

makeKindEnv :: [(SLoc, (TypeConstructor, KindRep))] -> KindEnv -> Either ErrMsg KindEnv
makeKindEnv = go where
    getRank :: KindExpr -> Int
    getRank Star = 0
    getRank (kin1 `KArr` kin2) = max (getRank kin1 + 1) (getRank kin2)
    unRep :: KindRep -> Either ErrMsg KindExpr
    unRep krep = do
        (kin, loc) <- case krep of
            RStar loc -> return (Star, loc)
            RKArr loc krep1 krep2 -> do
                kin1 <- unRep krep1
                kin2 <- unRep krep2
                return (kin1 `KArr` kin2, loc)
            RKPrn loc krep -> do
                kin <- unRep krep
                return (kin, loc)
        if getRank kin > 1
            then Left ("*** desugaring-error[" ++ pprint 0 loc "]:\n  ? the higher-order kind expression is not allowed.")
            else return kin
    go :: [(SLoc, (TypeConstructor, KindRep))] -> KindEnv -> Either ErrMsg KindEnv
    go [] kind_env = return kind_env
    go ((loc, (tcon, krep)) : triples) kind_env
        | TC_Named tc <- tcon, head tc `elem` ['A' .. 'Z'] = Left ("*** desugaring-error[" ++ pprint 0 loc "]:\n  ? the identifier of a type constructor must be started with a small letter.")
        | otherwise = case Map.lookup tcon kind_env of
            Just _ -> Left ("*** desugaring-error[" ++ pprint 0 loc "]:\n  ? it is wrong to redeclare an already declared type construtor.")
            Nothing -> do
                kin <- unRep krep
                go triples (Map.insert tcon kin kind_env)

makeTypeEnv :: KindEnv -> [(SLoc, (DataConstructor, TypeRep))] -> TypeEnv -> Either ErrMsg TypeEnv
makeTypeEnv kind_env = go where
    applyModusPonens :: KindExpr -> KindExpr -> Either ErrMsg KindExpr
    applyModusPonens (kin1 `KArr` kin2) kin3
        | kin1 == kin3 = Right kin2
    applyModusPonens (kin1 `KArr` kin2) kin3 = Left ("  ? couldn't solve `" ++ pprint 0 kin1 ("\' ~ `" ++ pprint 0 kin3 "\'"))
    applyModusPonens Star kin1 = Left ("  ? coudln't solve `type\' ~ `" ++ pprint 1 kin1 " -> _\'")
    unRep :: TypeRep -> Either ErrMsg (KindExpr, MonoType LargeId)
    unRep trep = case trep of
        RTyVar loc tvrep -> return (Star, TyVar tvrep)
        RTyCon loc (TC_Named "string") -> return (Star, mkTyList mkTyChr)
        RTyCon loc type_constructor -> case Map.lookup type_constructor kind_env of
            Nothing -> Left ("*** desugaring-error[" ++ pprint 0 loc ("]:\n  ? the type constructor `" ++ showsPrec 0 type_constructor "hasn't declared.\n"))
            Just kin -> return (kin, TyCon (TCon type_constructor kin))
        RTyApp loc trep1 trep2 -> do
            (kin1, typ1) <- unRep trep1
            (kin2, typ2) <- unRep trep2
            case applyModusPonens kin1 kin2 of
                Left msg -> Left ("*** desugaring-error[" ++ pprint 0 loc ("]:\n " ++ msg ++ ".\n"))
                Right kin -> return (kin, TyApp typ1 typ2)
        RTyPrn loc trep -> unRep trep
    generalize :: MonoType LargeId -> PolyType
    generalize typ = Forall tvars (indexify typ) where
        getFreeTVs :: MonoType LargeId -> Set.Set LargeId
        getFreeTVs (TyVar tvar) = Set.singleton tvar
        getFreeTVs (TyCon tcon) = Set.empty
        getFreeTVs (TyApp typ1 typ2) = getFreeTVs typ1 `Set.union` getFreeTVs typ2
        getFreeTVs (TyMTV mtv) = Set.empty
        tvars :: [LargeId]
        tvars = Set.toAscList (getFreeTVs typ)
        indexify :: MonoType LargeId -> MonoType Int
        indexify (TyVar tvar) = maybe (error "unreachable!") TyVar $ tvar `List.elemIndex` tvars
        indexify (TyCon tcon) = TyCon tcon
        indexify (TyApp typ1 typ2) = TyApp (indexify typ1) (indexify typ2)
        indexify (TyMTV mtv) = TyMTV mtv
    hasValidHead :: MonoType LargeId -> Bool
    hasValidHead = go2 . go1 where
        go1 :: MonoType LargeId -> MonoType LargeId
        go1 (TyApp (TyApp (TyCon (TCon TC_Arrow _)) typ1) typ2) = go1 typ2
        go1 typ1 = typ1
        go2 :: MonoType LargeId -> Bool
        go2 (TyCon tcon) = case tcon of
            TCon (TC_Named "char") _ -> False
            TCon (TC_Named "list") _ -> False
            TCon (TC_Named "nat") _ -> False
            _ -> True
        go2 (TyApp typ _) = go2 typ
        go2 _ = False
    go :: [(SLoc, (DataConstructor, TypeRep))] -> TypeEnv -> Either ErrMsg TypeEnv
    go [] type_env = return type_env
    go ((loc, (con, trep)) : triples) type_env = case Map.lookup con type_env of
        Nothing -> do
            (kin, typ) <- unRep trep
            if kin == Star
                then if hasValidHead typ
                    then go triples (Map.insert con (generalize typ) type_env)
                    else Left ("*** desugaring-error[" ++ pprint 0 loc ("]:\n  ? the head of the type `" ++ showsPrec 0 con "\' is invalid."))
                else Left ("*** desugaring-error[" ++ pprint 0 loc ("]:\n  ? couldn't solve `" ++ pprint 0 kin "\' ~ `type\'."))
        _ -> Left ("*** desugaring-error[" ++ pprint 0 loc ("]:\n  ? it is wrong to redeclare the already declared constant `" ++ showsPrec 0 con "\'."))

desugarTerm :: MonadUnique m => TermRep -> StateT (Map.Map LargeId IVar) m (TermExpr DataConstructor SLoc)
desugarTerm (R_wc loc1) = do
    return (Con loc1 DC_wc)
desugarTerm (RVar loc1 var_rep) = do
    env <- get
    case Map.lookup var_rep env of
        Nothing -> do
            var <- getUnique
            put (Map.insert var_rep var env)
            return (Var loc1 var)
        Just var -> return (Var loc1 var)
desugarTerm (RCon loc1 (DC_Named con)) = do
    env <- get
    case Map.lookup con env of
        Nothing -> return (Con loc1 (DC_Named con))
        Just var -> return (Var loc1 var)
desugarTerm (RCon loc1 con) = return (Con loc1 con)
desugarTerm (RApp loc1 term_rep_1 term_rep_2) = do
    term_1 <- desugarTerm term_rep_1
    term_2 <- desugarTerm term_rep_2
    return (App loc1 term_1 term_2)
desugarTerm (RAbs loc1 var_rep term_rep) = do
    var <- getUnique
    env <- get
    case Map.lookup var_rep env of
        Nothing -> do
            put (Map.insert var_rep var env)
            term <- desugarTerm term_rep
            modify (Map.delete var_rep)
            return (Lam loc1 var term)
        Just var' -> do
            put (Map.insert var_rep var (Map.delete var_rep env))
            term <- desugarTerm term_rep
            modify (Map.insert var_rep var' . Map.delete var_rep)
            return (Lam loc1 var term)
desugarTerm (RPrn loc1 term_rep) = desugarTerm term_rep

desugarProgram :: MonadUnique m => KindEnv -> TypeEnv -> String -> [DeclRep] -> ExceptT ErrMsg m (Program (TermExpr DataConstructor SLoc))
desugarProgram kind_env type_env file_name program
    = case makeKindEnv [ (loc, (tcon, krep)) | RKindDecl loc tcon krep <- program ] kind_env of
        Left err_msg -> throwE err_msg
        Right kind_env' -> case makeTypeEnv kind_env' [ (loc, (con, trep)) | RTypeDecl loc con trep <- program ] type_env of
            Left err_msg -> throwE err_msg
            Right type_env' -> do
                facts' <- lift (mapM (fmap fst . flip runStateT Map.empty . desugarTerm) [ fact_rep | RFactDecl _ fact_rep <- program ])
                return (kind_env' `seq` type_env' `seq` facts' `seq` Program { _KindDecls = kind_env', _TypeDecls = type_env', _FactDecls = facts', moduleName = file_name })

desugarQuery :: MonadUnique m => TermRep -> ExceptT ErrMsg m (TermExpr DataConstructor SLoc, Map.Map LargeId IVar)
desugarQuery query0 = runStateT (desugarTerm query0) Map.empty
