module Hol.ALPHA1.Back.HOPU.Bind where

import Hol.ALPHA1.Back.Base.Labeling
import Hol.ALPHA1.Back.Base.Constant
import Hol.ALPHA1.Back.Base.TermNode
import Hol.ALPHA1.Back.Base.TermNode.Util
import Hol.ALPHA1.Back.Base.VarBinding
import Hol.ALPHA1.Back.HOPU.Select
import Hol.ALPHA1.Back.HOPU.Util
import Hol.ALPHA1.Front.Header
import Control.Monad.Trans.Class
import Control.Monad.Trans.Except
import Control.Monad.Trans.State.Strict
import qualified Data.List as List
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set

bind :: GenUniqueM m => LogicVar -> TermNode -> [TermNode] -> Int -> StateT Labeling (ExceptT HopuFail m) (LVarSubst, TermNode)
bind var rhs parameters lambda = do
    labeling <- get
    go (lookupLabel var labeling) (rewrite HNF rhs) (arguments lambda) lambda
    where
        arguments :: Int -> [TermNode]
        arguments lambda = [ rewriteWithSusp param 0 lambda [] NF | param <- parameters ] ++ map mkNIdx [lambda, lambda - 1 .. 1]
        translate :: GenUniqueM m => ScopeLevel -> [TermNode] -> [TermNode] -> Int -> StateT Labeling (ExceptT HopuFail m) (LVarSubst, [TermNode])
        translate var_label [] lhs_arguments lambda = return (mempty, [])
        translate var_label (rhs_tail_element : rhs_tail) lhs_arguments lambda = do
            (subst, lhs_tail_element) <- go var_label (rewrite HNF rhs_tail_element) lhs_arguments lambda
            (theta, lhs_tail) <- translate var_label (applyBinding subst rhs_tail) lhs_arguments lambda
            return (theta <> subst, applyBinding theta lhs_tail_element : lhs_tail)
        go :: GenUniqueM m => ScopeLevel -> TermNode -> [TermNode] -> Int -> StateT Labeling (ExceptT HopuFail m) (LVarSubst, TermNode)
        go var_label rhs@(NCon (DC (DC_NatL _))) _ _ = return (mempty, rhs)
        go var_label rhs lhs_arguments lambda
            | (lambda', rhs') <- viewNestedNAbs rhs
            , lambda' > 0
            = do
                (subst, lhs') <- go var_label rhs' (arguments (lambda + lambda')) (lambda + lambda')
                return (subst, makeNestedNAbs lambda' lhs')
            | (rhs_head, rhs_tail) <- unfoldlNApp rhs
            , isRigid rhs_head
            = do
                labeling <- get
                let get_lhs_head
                        | NCon con <- rhs_head
                        , var_label >= lookupLabel con labeling
                        = return rhs_head
                        | Just idx <- rhs_head `List.elemIndex` lhs_arguments
                        = return (mkNIdx (length lhs_arguments - idx))
                        | otherwise
                        = lift (throwE FlexRigidFail)
                lhs_head <- get_lhs_head
                (subst, lhs_tail) <- translate var_label rhs_tail lhs_arguments lambda
                return (subst, foldlNApp lhs_head lhs_tail)
            | (LVar var', rhs_tail) <- unfoldlNApp rhs
            = if var == var'
                then lift (throwE OccursCheckFail)
                else do
                    labeling <- get
                    let isty = isTypeLVar var || isTypeLVar var'
                        rhs_arguments = map (rewrite NF) rhs_tail
                        common_arguments = Set.toList (Set.fromList lhs_arguments `Set.intersection` Set.fromList rhs_arguments)
                    if isPatternRespectTo var' rhs_arguments labeling
                        then do
                            (lhs_inner, rhs_inner) <- case var_label `compare` lookupLabel var' labeling of
                                LT -> do
                                    selected_rhs_parameters <- lhs_arguments `up` var'
                                    selected_lhs_parameters <- selected_rhs_parameters `down` lhs_arguments
                                    return (selected_lhs_parameters, selected_rhs_parameters)
                                geq -> do
                                    selected_lhs_parameters <- rhs_arguments `up` var
                                    selected_rhs_parameters <- selected_lhs_parameters `down` rhs_arguments
                                    return (selected_lhs_parameters, selected_rhs_parameters)
                            lhs_outer <- common_arguments `down` lhs_arguments
                            rhs_outer <- common_arguments `down` rhs_arguments
                            common_head <- getNewLVar isty var_label
                            case var' +-> makeNestedNAbs (length rhs_tail) (foldlNApp common_head (rhs_inner ++ rhs_outer)) of
                                Nothing -> lift (throwE OccursCheckFail)
                                Just theta -> do
                                    modify (zonkLVar theta)
                                    return (theta, foldlNApp common_head (lhs_inner ++ lhs_outer))
                        else do
                            (subst, lhs_tail) <- liftCatch catchE (translate var_label rhs_tail lhs_arguments lambda) (\_ -> lift (throwE NotAPattern))
                            return (subst, foldlNApp (mkLVar var') lhs_tail)
            | otherwise
            = lift (throwE BindFail)
