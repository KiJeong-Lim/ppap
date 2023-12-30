module Aladdin.Front.TypeChecker.Util where

import Aladdin.Front.Header
import Control.Monad
import Control.Monad.Trans.Class
import Control.Monad.Trans.Except
import Control.Monad.Trans.State.Strict
import qualified Data.List as List
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Y.Base
import Z.Utils

infix 4 +->

data TypeError
    = KindsAreMismatched (MonoType Int, KindExpr) (MonoType Int, KindExpr)
    | OccursCheckFailed MetaTVar (MonoType Int)
    | TypesAreMismatched (MonoType Int) (MonoType Int)
    deriving ()

newtype TypeSubst
    = TypeSubst { getTypeSubst :: Map.Map MetaTVar (MonoType Int) }
    deriving ()

class HasMTVar a where
    getFreeMTVs :: a -> Set.Set MetaTVar -> Set.Set MetaTVar
    substMTVars :: TypeSubst -> a -> a

class IsInt a where
    fromInt :: Int -> a
    toInt :: a -> Int

instance IsInt Int where
    fromInt = id
    toInt = id

instance IsInt tvar => HasMTVar (MonoType tvar) where
    getFreeMTVs (TyMTV mtv) = Set.insert mtv
    getFreeMTVs (TyVar tvar) = id
    getFreeMTVs (TyCon tcon) = id
    getFreeMTVs (TyApp typ1 typ2) = getFreeMTVs typ1 . getFreeMTVs typ2
    substMTVars (TypeSubst { getTypeSubst = mapsto }) = go where
        convert :: IsInt tvar => MonoType Int -> MonoType tvar
        convert (TyVar tvar) = TyVar (fromInt tvar)
        convert (TyCon tcon) = TyCon tcon
        convert (TyApp typ1 typ2) = TyApp (convert typ1) (convert typ2)
        convert (TyMTV mtv) = TyMTV mtv
        go :: IsInt tvar => MonoType tvar -> MonoType tvar
        go typ = case typ of
            TyMTV mtv -> maybe typ convert (Map.lookup mtv mapsto)
            TyApp typ1 typ2 -> TyApp (go typ1) (go typ2)
            TyVar tvar -> TyVar tvar
            TyCon tcon -> TyCon tcon

instance HasMTVar a => HasMTVar [a] where
    getFreeMTVs = flip (foldr getFreeMTVs)
    substMTVars = map . substMTVars

instance HasMTVar b => HasMTVar (a, b) where
    getFreeMTVs = snd . fmap getFreeMTVs
    substMTVars = fmap . substMTVars

instance HasMTVar a => HasMTVar (Map.Map k a) where
    getFreeMTVs = getFreeMTVs . Map.elems
    substMTVars = Map.map . substMTVars

instance Semigroup TypeSubst where
    theta2 <> theta1 = TypeSubst { getTypeSubst = Map.map (substMTVars theta2) (getTypeSubst theta1) `Map.union` (getTypeSubst theta2) }

instance Monoid TypeSubst where
    mempty = TypeSubst { getTypeSubst = Map.empty }

(+->) :: MetaTVar -> MonoType Int -> Either TypeError TypeSubst
mtv +-> typ 
    | TyMTV mtv == typ = return mempty
    | mtv `Set.member` getFMTVs typ = Left (OccursCheckFailed mtv typ)
    | getKind (TyMTV mtv) == getKind typ = return (TypeSubst (Map.singleton mtv typ))
    | otherwise = Left (KindsAreMismatched (TyMTV mtv, getKind (TyMTV mtv)) (typ, getKind typ))

getFMTVs :: HasMTVar a => a -> Set.Set MetaTVar
getFMTVs = flip getFreeMTVs Set.empty

getKind :: MonoType Int -> KindExpr
getKind = maybe (error "`getKind\'") id . go where
    go :: MonoType Int -> Maybe KindExpr
    go (TyVar _) = return Star
    go (TyCon (TCon _ kin)) = return kin
    go (TyApp typ1 typ2) = do
        (kin1 `KArr` kin2) <- go typ1
        return kin2
    go (TyMTV _) = return Star

showMonoType :: Map.Map MetaTVar LargeId -> MonoType Int -> String -> String
showMonoType name_env = go 0 where
    go :: Precedence -> MonoType Int -> String -> String
    go prec (TyApp (TyApp (TyCon (TCon TC_Arrow _)) typ1) typ2)
        | prec <= 0 = go 1 typ1 . strstr " -> " . go 0 typ2
        | otherwise = strstr "(" . go 1 typ1 . strstr " -> " . go 0 typ2 . strstr ")"
    go prec (TyApp typ1 typ2)
        | prec <= 1 = go 1 typ1 . strstr " " . go 2 typ2
        | otherwise = strstr "(" . go 1 typ1 . strstr " " . go 2 typ2 . strstr ")"
    go prec (TyCon con)
        = pprint 0 con
    go prec (TyVar var)
        = strstr "#" . showsPrec 0 var
    go prec (TyMTV mtv)
        = case Map.lookup mtv name_env of
            Nothing -> strstr "?_" . showsPrec 0 mtv
            Just name -> strstr "?" . strstr name

instantiateScheme :: GenUniqueM m => PolyType -> StateT (Map.Map MetaTVar LargeId) (ExceptT ErrMsg m) ([MetaTVar], MonoType Int)
instantiateScheme = go where
    loop :: [MonoType Int] -> MonoType Int -> MonoType Int
    loop tvars (TyVar idx) = tvars !! idx
    loop tvars (TyCon tcon) = TyCon tcon
    loop tvars (TyApp typ1 typ2) = TyApp (loop tvars typ1) (loop tvars typ2)
    loop tvars (TyMTV mtv) = TyMTV mtv 
    go :: GenUniqueM m => PolyType -> StateT (Map.Map MetaTVar LargeId) (ExceptT ErrMsg m) ([MetaTVar], MonoType Int)
    go (Forall tvars typ) = do
        mtvs <- mapM getNewMTV tvars
        return (mtvs, loop (map TyMTV mtvs) typ)

getNewMTV :: GenUniqueM m => LargeId -> StateT (Map.Map MetaTVar LargeId) (ExceptT ErrMsg m) MetaTVar
getNewMTV largeid
    = do
        used_mtvs_0 <- get
        mtv <- getNewUnique
        let name = makeName used_mtvs_0 largeid
        put (Map.insert mtv name used_mtvs_0)
        return mtv
    where
        makeName :: Map.Map MetaTVar LargeId -> LargeId -> LargeId
        makeName used_mtvs smallid = go 0 where
            go :: Int -> LargeId
            go n = if name `elem` Map.elems used_mtvs then go (n + 1) else name where
                name :: String
                name = smallid ++ "_" ++ show n

zonkMTV :: TypeSubst -> TermExpr (DataConstructor, [MonoType Int]) (SLoc, MonoType Int) -> TermExpr (DataConstructor, [MonoType Int]) (SLoc, MonoType Int)
zonkMTV theta = go where
    go :: TermExpr (DataConstructor, [MonoType Int]) (SLoc, MonoType Int) -> TermExpr (DataConstructor, [MonoType Int]) (SLoc, MonoType Int)
    go (IVar (loc, typ) var) = IVar (loc, substMTVars theta typ) var
    go (DCon (loc, typ) (con, tapps)) = DCon (loc, substMTVars theta typ) (con, substMTVars theta tapps)
    go (IApp (loc, typ) term1 term2) = IApp (loc, substMTVars theta typ) (go term1) (go term2)
    go (IAbs (loc, typ) var term) = IAbs (loc, substMTVars theta typ) var (go term)

mkTyErr :: Map.Map MetaTVar LargeId -> SLoc -> ((MonoType Int, MonoType Int), TypeError) -> ErrMsg
mkTyErr used_mtvs loc ((actual_typ, expected_typ), typ_error) = case typ_error of
    KindsAreMismatched (typ1, kin1) (typ2, kin2) -> concat
        [ "*** typechecking-error[" ++ pprint 0 loc "]:\n"
        , "  ? expected_typ = `" ++ showMonoType used_mtvs expected_typ ("\', actual_typ = `" ++ showMonoType used_mtvs actual_typ "\'.\n")
        , "  ? couldn't solve the equation `" ++ showMonoType used_mtvs typ1 ("\' ~ `" ++ showMonoType used_mtvs typ2 "\',\n")
        , "  ? because the kind of the L.H.S. is `" ++ pprint 0 kin1 ("\' but the kind of the R.H.S. is `" ++ pprint 0 kin2 "\'.")
        ]
    OccursCheckFailed mtv1 typ2 -> concat
        [ "*** typechecking-error[" ++ pprint 0 loc "]:\n"
        , "  ? expected_typ = `" ++ showMonoType used_mtvs expected_typ ("\', actual_typ = `" ++ showMonoType used_mtvs actual_typ "\'.\n")
        , "  ? couldn't solve the equation `" ++ showMonoType used_mtvs (TyMTV mtv1) ("\' ~ `" ++ showMonoType used_mtvs typ2 "\',\n")
        , "  ? because occurs check failed."
        ]
    TypesAreMismatched typ1 typ2 -> concat
        [ "*** typechecking-error[" ++ pprint 0 loc "]:\n"
        , "  ? expected_typ = `" ++ showMonoType used_mtvs expected_typ ("\', actual_typ = `" ++ showMonoType used_mtvs actual_typ "\'.\n")
        , "  ? couldn't solve the equation `" ++ showMonoType used_mtvs typ1 ("\' ~ `" ++ showMonoType used_mtvs typ2 "\',\n")
        , "  ? because the types `" ++ showMonoType used_mtvs typ1 ("\' and `" ++ showMonoType used_mtvs typ2 "\' are non-unifiable.")
        ]
