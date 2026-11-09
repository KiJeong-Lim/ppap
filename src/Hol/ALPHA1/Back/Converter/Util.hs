module Hol.ALPHA1.Back.Converter.Util where

import Hol.ALPHA1.Back.Base.TermNode
import Hol.ALPHA1.Back.Base.TermNode.Util
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

unFoldIApp :: TermExpr dcon annot -> (TermExpr dcon annot, [TermExpr dcon annot])
unFoldIApp = flip go [] where
    go :: TermExpr dcon annot -> [TermExpr dcon annot] -> (TermExpr dcon annot, [TermExpr dcon annot])
    go (IApp annot term1 term2) terms = go term1 (term2 : terms)
    go term terms = (term, terms)

reduceTermExpr :: GenUniqueM m => TermExpr dcon annot -> m (TermExpr dcon annot)
reduceTermExpr term = do
    term' <- reduceHeadTermExpr term
    case term' of
        IApp annot term1 term2 -> IApp annot <$> reduceTermExpr term1 <*> reduceTermExpr term2
        IAbs annot var body -> IAbs annot var <$> reduceTermExpr body
        _ -> return term'

reduceHeadTermExpr :: GenUniqueM m => TermExpr dcon annot -> m (TermExpr dcon annot)
reduceHeadTermExpr = go where
    go :: GenUniqueM m => TermExpr dcon annot -> m (TermExpr dcon annot)
    go (IApp annot term1 term2) = do
        term1' <- go term1
        case term1' of
            IAbs _ var body -> substitute var term2 body >>= go
            _ -> return (IApp annot term1' term2)
    go term = return term
    freeVars :: TermExpr dcon annot -> Set.Set IVar
    freeVars (IVar _ var) = Set.singleton var
    freeVars (DCon _ _) = Set.empty
    freeVars (IApp _ term1 term2) = freeVars term1 `Set.union` freeVars term2
    freeVars (IAbs _ var body) = Set.delete var (freeVars body)
    rename :: IVar -> IVar -> TermExpr dcon annot -> TermExpr dcon annot
    rename old new term = case term of
        IVar annot var -> IVar annot (if var == old then new else var)
        DCon _ _ -> term
        IApp annot term1 term2 -> IApp annot (rename old new term1) (rename old new term2)
        IAbs annot var body
            | var == old -> term
            | otherwise -> IAbs annot var (rename old new body)
    substitute :: GenUniqueM m => IVar -> TermExpr dcon annot -> TermExpr dcon annot -> m (TermExpr dcon annot)
    substitute var argument = subst where
        free = freeVars argument
        subst term = case term of
            IVar _ var'
                | var == var' -> return argument
            IApp annot term1 term2 -> IApp annot <$> subst term1 <*> subst term2
            IAbs annot var' body
                | var == var' -> return term
                | var' `Set.member` free -> do
                    fresh <- getNewUnique
                    IAbs annot fresh <$> subst (rename var' fresh body)
                | otherwise -> IAbs annot var' <$> subst body
            _ -> return term
