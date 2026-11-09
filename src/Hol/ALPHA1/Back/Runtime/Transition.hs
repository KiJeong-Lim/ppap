module Hol.ALPHA1.Back.Runtime.Transition where

import Hol.ALPHA1.Back.Base.Constant
import Hol.ALPHA1.Back.Base.Labeling
import Hol.ALPHA1.Back.Base.TermNode
import Hol.ALPHA1.Back.Base.TermNode.Util
import Hol.ALPHA1.Back.Base.VarBinding
import Hol.ALPHA1.Back.HOPU.Main
import Hol.ALPHA1.Back.HOPU.Util
import Hol.ALPHA1.Back.Runtime.Instantiation
import Hol.ALPHA1.Back.Runtime.LogicalOperator
import Hol.ALPHA1.Back.Runtime.Util
import Hol.ALPHA1.Front.Header
import Control.Monad
import Control.Monad.IO.Class
import Control.Monad.Trans.Class
import Control.Monad.Trans.Except
import Control.Monad.Trans.State.Strict
import Data.IORef
import qualified Data.List as List
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set

runTransition :: RuntimeEnv -> [Clause] -> Set.Set LogicVar -> Stack -> ExceptT KernelErr (UniqueGenT IO) Satisfied
runTransition env program free_lvars = go where
    search :: [Clause] -> ScopeLevel -> Constant -> [TermNode] -> Context -> [Cell] -> ExceptT KernelErr (UniqueGenT IO) Stack
    search facts level predicate args ctx cells = do
        call_id <- getNewUnique
        return
            [ (ctx { _ContextThreadId = call_id }, MatchClause facts level (foldlNApp (mkNCon predicate) args) call_id fact : cells)
            | Clause fact predicate' <- facts ++ program
            , maybe True (== predicate) predicate'
            ]
    match :: [Clause] -> ScopeLevel -> Goal -> CallId -> Fact -> Context -> [Cell] -> Stack -> ExceptT KernelErr (UniqueGenT IO) Satisfied
    match facts level goal call_id fact ctx cells stack = do
        ((goal', new_goal), labeling) <- runStateT (instantiateFact fact level) (_CurrentLabeling ctx)
        case (unfoldlNApp (rewrite HNF goal), unfoldlNApp (rewrite HNF goal')) of
            ((NCon predicate, args), (NCon predicate', args'))
                | predicate == predicate' -> do
                    hopu_output <- if length args == length args' then lift (runHOPU labeling (zipWith (:=?=:) args args' ++ _LeftConstraints ctx)) else throwE (BadFactGiven goal')
                    case hopu_output of
                        Nothing -> go stack
                        Just (new_disagreements, HopuSol new_labeling subst) -> do
                            let ctx' = ctx { _TotalVarBinding = extendBinding subst (_TotalVarBinding ctx), _CurrentLabeling = new_labeling, _LeftConstraints = new_disagreements, _ContextThreadId = call_id }
                            go ((ctx', zonkLVar subst (mkCell facts level new_goal call_id : cells)) : stack)
            _ -> go stack
    dispatch :: Context -> [Clause] -> ScopeLevel -> (TermNode, [TermNode]) -> CallId -> [Cell] -> Stack -> ExceptT KernelErr (UniqueGenT IO) Satisfied
    dispatch ctx facts level (NCon predicate, args) call_id cells stack
        | DC (DC_LO logical_operator) <- predicate
        = do
            stack' <- runLogicalOperator logical_operator args ctx facts level call_id cells stack
            go stack'
        | otherwise
        = do
            stack' <- search facts level predicate args ctx cells
            go (stack' ++ stack)
    dispatch ctx facts level (t, ts) call_id cells stack = throwE (BadGoalGiven (foldlNApp t ts))
    go :: Stack -> ExceptT KernelErr (UniqueGenT IO) Satisfied
    go [] = return False
    go ((ctx, MatchClause facts level goal call_id fact : cells) : stack) = match facts level goal call_id fact ctx cells stack
    go ((ctx, cells) : stack) = do
        keep_going <- liftIO (_PutStr env ctx (showsCurrentState free_lvars ctx cells stack ""))
        unless keep_going (throwE QuitRequested)
        case cells of
            [] -> do
                want_more <- liftIO (_Answer env ctx)
                if want_more then go stack else return True
            cell : cells -> dispatch ctx (_LocalFacts cell) (_ScopeLevel cell) (unfoldlNApp (rewrite HNF (_WantedGoal cell))) (_CellCallId cell) cells stack
