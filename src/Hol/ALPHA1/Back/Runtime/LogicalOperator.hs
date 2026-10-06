module Hol.ALPHA1.Back.Runtime.LogicalOperator where

import Hol.ALPHA1.Back.Base.Constant
import Hol.ALPHA1.Back.Base.Labeling
import Hol.ALPHA1.Back.Base.TermNode
import Hol.ALPHA1.Back.Base.TermNode.Util
import Hol.ALPHA1.Back.Base.VarBinding
import Hol.ALPHA1.Back.HOPU.Main
import Hol.ALPHA1.Back.HOPU.Util
import Hol.ALPHA1.Back.Runtime.Arith
import Hol.ALPHA1.Back.Runtime.Util
import Hol.ALPHA1.Front.Header
import Control.Monad.IO.Class
import Control.Monad.Trans.Class
import Control.Monad.Trans.Except
import Control.Monad.Trans.State.Strict
import Data.IORef
import Z.System.Shelly

runLogicalOperator :: LogicalOperator -> [TermNode] -> Context -> [Fact] -> ScopeLevel -> CallId -> [Cell] -> Stack -> ExceptT KernelErr (UniqueGenT IO) Stack
runLogicalOperator LO_true [] ctx facts level call_id cells stack = return ((ctx, cells) : stack)
runLogicalOperator LO_fail [] ctx facts level call_id cells stack = return stack
runLogicalOperator LO_debug [loc_str] ctx facts level call_id cells stack = runDebugger loc_str ctx facts level call_id cells stack
runLogicalOperator LO_cut [] ctx facts level call_id cells stack = return ((ctx, cells) : [ (ctx', cells') | (ctx', cells') <- stack, _ContextThreadId ctx' < call_id ])
runLogicalOperator LO_and [goal1, goal2] ctx facts level call_id cells stack = return ((ctx, mkCell facts level goal1 call_id : mkCell facts level goal2 call_id : cells) : stack)
runLogicalOperator LO_or [goal1, goal2] ctx facts level call_id cells stack = return ((ctx, mkCell facts level goal1 call_id : cells) : (ctx, mkCell facts level goal2 call_id : cells) : stack)
runLogicalOperator LO_imply [fact1, goal2] ctx facts level call_id cells stack = return ((ctx, mkCell (fact1 : facts) level goal2 call_id : cells) : stack)
runLogicalOperator LO_sigma [goal1] ctx facts level call_id cells stack = do
    uni <- getNewUnique
    let var = LV_Unique uni
    return ((ctx { _CurrentLabeling = enrollLabel var level (_CurrentLabeling ctx) }, mkCell facts level (mkNApp goal1 (mkLVar var)) call_id : cells) : stack)
runLogicalOperator LO_pi [goal1] ctx facts level call_id cells stack = do
    uni <- getNewUnique
    let con = DC (DC_Unique uni)
    return ((ctx { _CurrentLabeling = enrollLabel con (level + 1) (_CurrentLabeling ctx) }, mkCell facts (level + 1) (mkNApp goal1 (mkNCon con)) call_id : cells) : stack)
runLogicalOperator (LO_Arith AP_Is) [lhs, rhs] ctx facts level call_id cells stack = do
    value <- either (throwE . ArithmeticFailure) return (evalNat rhs)
    output <- lift (runHOPU (_CurrentLabeling ctx) ((lhs :=?=: mkNCon (DC_NatL value)) : _LeftConstraints ctx))
    case output of
        Nothing -> return stack
        Just (disagreements, HopuSol labeling subst) -> do
            let ctx' = ctx { _TotalVarBinding = zonkLVar subst (_TotalVarBinding ctx), _CurrentLabeling = labeling, _LeftConstraints = disagreements }
            return ((ctx', zonkLVar subst cells) : stack)
runLogicalOperator (LO_Arith predicate) [lhs, rhs] ctx facts level call_id cells stack = do
    value1 <- either (throwE . ArithmeticFailure) return (evalNat lhs)
    value2 <- either (throwE . ArithmeticFailure) return (evalNat rhs)
    return (if compareNat predicate value1 value2 then (ctx, cells) : stack else stack)
runLogicalOperator logical_operator args ctx facts level call_id cells stack = throwE (BadGoalGiven (foldlNApp (mkNCon logical_operator) args))

runDebugger :: TermNode -> Context -> [Fact] -> ScopeLevel -> CallId -> [Cell] -> Stack -> ExceptT KernelErr (UniqueGenT IO) Stack
runDebugger loc_str ctx facts level call_id cells stack = do
    liftIO $ writeIORef (_debuggindModeOn ctx) True
    liftIO $ putStrLn ("*** debugger called with " ++ shows loc_str "")
    return ((ctx, cells) : stack)
