module Aladdin.Back.HOPU.Simplify where

import Aladdin.Back.Base.Labeling
import Aladdin.Back.Base.TermNode
import Aladdin.Back.Base.TermNode.Util
import Aladdin.Back.Base.VarBinding
import Aladdin.Back.HOPU.Bind
import Aladdin.Back.HOPU.MkSubst
import Aladdin.Back.HOPU.Select
import Aladdin.Back.HOPU.Util
import Aladdin.Front.Header
import Control.Monad.Trans.Class
import Control.Monad.Trans.Except
import Control.Monad.Trans.State.Strict
import qualified Data.List as List
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set

type HasChanged = Bool

simplify :: GenUniqueM m => [Disagreement] -> Labeling -> StateT HasChanged (ExceptT HopuFail m) ([Disagreement], HopuSol)
simplify = flip loop mempty . zip (repeat 0) where
    loop :: GenUniqueM m => [(Int, Disagreement)] -> LVarSubst -> Labeling -> StateT HasChanged (ExceptT HopuFail m) ([Disagreement], HopuSol)
    loop [] subst labeling = return ([], HopuSol labeling subst)
    loop ((l, lhs :=?=: rhs) : disagreements) subst labeling = dispatch l (applyBinding subst (rewrite NF lhs)) (applyBinding subst (rewrite NF rhs)) where
        dispatch :: GenUniqueM m => Int -> TermNode -> TermNode -> StateT HasChanged (ExceptT HopuFail m) ([Disagreement], HopuSol)
        dispatch l lhs rhs
            | (lambda1, lhs') <- viewNestedNAbs lhs
            , (lambda2, rhs') <- viewNestedNAbs rhs
            , lambda1 > 0 && lambda2 > 0
            = (\lambda -> dispatch (l + lambda) (makeNestedNAbs (lambda1 - lambda) lhs') (makeNestedNAbs (lambda2 - lambda) rhs')) $! min lambda1 lambda2
            | (lambda1, lhs') <- viewNestedNAbs lhs
            , (rhs_head, rhs_tail) <- unfoldlNApp rhs
            , lambda1 > 0 && isRigid rhs_head
            = dispatch (l + lambda1) lhs' (foldlNApp (rewriteWithSusp rhs_head 0 lambda1 [] HNF) ([ mkSusp rhs_tail_element 0 lambda1 [] | rhs_tail_element <- rhs_tail ] ++ map mkNIdx [lambda1, lambda1 - 1 .. 1]))
            | (lhs_head, lhs_tail) <- unfoldlNApp lhs
            , (lambda2, rhs') <- viewNestedNAbs rhs
            , isRigid lhs_head && lambda2 > 0
            = dispatch (l + lambda2) (foldlNApp (rewriteWithSusp lhs_head 0 lambda2 [] HNF) ([ mkSusp lhs_tail_element 0 lambda2 [] | lhs_tail_element <- lhs_tail ] ++ map mkNIdx [lambda2, lambda2 - 1 .. 1])) rhs'
            | (lhs_head, lhs_tail) <- unfoldlNApp lhs
            , (rhs_head, rhs_tail) <- unfoldlNApp rhs
            , isRigid lhs_head && isRigid rhs_head
            = if lhs_head == rhs_head && length lhs_tail == length rhs_tail
                then loop ([ (l, lhs' :=?=: rhs') | (lhs', rhs') <- zip lhs_tail rhs_tail ] ++ disagreements) subst labeling
                else lift (throwE RigidRigidFail)
            | (LVar var, parameters) <- unfoldlNApp lhs
            , isPatternRespectTo var parameters labeling
            = do
                output <- lift (mksubst var rhs parameters labeling)
                case output of
                    Nothing -> solveNext
                    Just (HopuSol labeling' subst') -> do
                        put True
                        loop (applyBinding subst' disagreements) (subst' <> subst) labeling'
            | (LVar var, parameters) <- unfoldlNApp rhs
            , isPatternRespectTo var parameters labeling
            = do
                output <- lift (mksubst var lhs parameters labeling)
                case output of
                    Nothing -> solveNext
                    Just (HopuSol labeling' subst') -> do
                        put True
                        loop (applyBinding subst' disagreements) (subst' <> subst) labeling'
            | otherwise
            = solveNext
        solveNext :: GenUniqueM m => StateT HasChanged (ExceptT HopuFail m) ([Disagreement], HopuSol)
        solveNext = do
            (disagreements', HopuSol labeling' subst') <- loop disagreements mempty labeling
            return (applyBinding subst' (makeNestedNAbs l lhs :=?=: makeNestedNAbs l rhs) : disagreements', HopuSol labeling' (subst' <> subst))
