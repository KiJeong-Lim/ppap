module Aladdin.Front.Desugarer.Main where

import Aladdin.Front.Analyzer.Grammar
import Aladdin.Front.Desugarer.ForKind
import Aladdin.Front.Desugarer.ForTerm
import Aladdin.Front.Desugarer.ForType
import Aladdin.Front.Header
import Control.Monad.Trans.Class
import Control.Monad.Trans.Except
import Control.Monad.Trans.State.Strict
import qualified Data.List as List
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Y.Base

desugarProgram :: GenUniqueM m => KindEnv -> TypeEnv -> String -> [DeclRep] -> ExceptT ErrMsg m (Program (TermExpr DataConstructor SLoc))
desugarProgram kind_env type_env file_name program
    = case makeKindEnv [ (loc, (tcon, krep)) | RKindDecl loc tcon krep <- program ] kind_env of
        Left err_msg -> throwE err_msg
        Right kind_env' -> case makeTypeEnv kind_env' [ (loc, (con, trep)) | RTypeDecl loc con trep <- program ] type_env of
            Left err_msg -> throwE err_msg
            Right type_env' -> do
                facts' <- lift (mapM (fmap fst . flip runStateT Map.empty . desugarTerm) [ fact_rep | RFactDecl _ fact_rep <- program ])
                return (kind_env' `seq` type_env' `seq` facts' `seq` Program { _KindDecls = kind_env', _TypeDecls = type_env', _FactDecls = facts', moduleName = file_name })

desugarQuery :: GenUniqueM m => TermRep -> ExceptT ErrMsg m (TermExpr DataConstructor SLoc, Map.Map LargeId IVar)
desugarQuery query0 = runStateT (desugarTerm query0) Map.empty
