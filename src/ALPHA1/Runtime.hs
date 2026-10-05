module ALPHA1.Runtime where

import ALPHA1.TermNode
import ALPHA1.HOPU
import ALPHA1.Constant
import ALPHA1.Header
import Control.Monad
import Control.Monad.IO.Class
import Control.Monad.Trans.Class
import Control.Monad.Trans.Except
import Control.Monad.Trans.State.Strict
import Data.IORef
import Data.Maybe
import qualified Data.List as List
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Z.Utils

type Fact = TermNode

type Goal = TermNode

type Stack = [(Context, [Cell])]

type Satisfied = Bool

type RunMore = Bool

type CallId = Unique

type Debugging = Bool

type KeepGoing = Bool

data KernelErr
    = BadGoalGiven TermNode
    | BadFactGiven TermNode
    | QuitRequested
    deriving ()

data Constraint
    = DisagreementConstraint Disagreement
    | EvalutionConstraint TermNode TermNode
    | ArithmeticConstraint !(TermNode)
    deriving (Eq, Ord)

data Cell
    = Cell
        { _GivenFacts :: [Fact]
        , _ScopeLevel :: ScopeLevel
        , _WantedGoal :: Goal
        , _CellCallId :: CallId
        }
    deriving ()

data Context
    = Context
        { _TotalVarBinding :: VarBinding
        , _CurrentLabeling :: Labeling
        , _LeftConstraints :: [Constraint]
        , _ContextThreadId :: CallId
        , _debuggindModeOn :: IORef Debugging
        }
    deriving ()

data RuntimeEnv
    = RuntimeEnv
        { _PutStr :: Context -> String -> IO KeepGoing
        , _Answer :: Context -> IO RunMore
        }
    deriving ()

instance ZonkLVar Context where
    zonkLVar theta ctx = Context
        { _TotalVarBinding = theta <> _TotalVarBinding ctx
        , _CurrentLabeling = zonkLVar theta (_CurrentLabeling ctx)
        , _LeftConstraints = zonkLVar theta (_LeftConstraints ctx)
        , _ContextThreadId = _ContextThreadId ctx
        , _debuggindModeOn = _debuggindModeOn ctx
        }

instance ZonkLVar Constraint where
    zonkLVar theta (DisagreementConstraint eqn) = DisagreementConstraint (bindVars theta eqn)
    zonkLVar theta (EvalutionConstraint lhs rhs) = EvalutionConstraint (bindVars theta lhs) (bindVars theta rhs)
    zonkLVar theta (ArithmeticConstraint arith) = ArithmeticConstraint (bindVars theta arith)

instance ZonkLVar Cell where
    zonkLVar theta (Cell facts level goal call_id) = Cell (bindVars theta facts) level (bindVars theta goal) call_id

instance Show Constraint where
    showsPrec prec (DisagreementConstraint eqn) = showsPrec prec eqn
    showsPrec prec (EvalutionConstraint lhs rhs) = showsPrec prec lhs . strstr " is " . showsPrec prec rhs
    showsPrec prec (ArithmeticConstraint arith) = showsPrec prec arith

mkCell :: [Fact] -> ScopeLevel -> Goal -> CallId -> Cell
mkCell facts level goal call_id = goal `seq` Cell { _GivenFacts = facts, _ScopeLevel = level, _WantedGoal = goal, _CellCallId = call_id }

showStackItem :: Set.Set LogicVar -> Indentation -> (Context, [Cell]) -> ShowS
showStackItem fvs space (ctx, cells) = strcat
    [ pindent space . strstr "+ progressings = " . plist (space + 4) [ strstr "?- " . shows goal . strstr " # call_id = " . shows call_id | Cell facts level goal call_id <- cells ] . nl
    , pindent space . strstr "+ context = Context" . nl
    , pindent (space + 4) . strstr "{ " . strstr "_scope_env = " . plist (space + 8) ([ shows (mkNCon c) . strstr " *--- " . shows level | (c, level) <- Map.toList (_ConLabel (_CurrentLabeling ctx)) ] ++ [ shows (mkLVar v) . strstr " *--- " . shows level | (v, level) <- Map.toList (_VarLabel (_CurrentLabeling ctx)), v `Set.member` fvs || not (v `Set.member` Map.keysSet (unVarBinding (_TotalVarBinding ctx))) ]) . nl
    , pindent (space + 4) . strstr ", " . strstr "_substitution = " . plist (space + 8) [ shows (LVar v) . strstr " |--> " . shows t | (v, t) <- Map.toList (unVarBinding (_TotalVarBinding ctx)), v `Set.member` fvs ] . nl
    , pindent (space + 4) . strstr ", " . strstr "_constraints = " . plist (space + 8) [ shows constraint | constraint <- _LeftConstraints ctx ] . nl
    , pindent (space + 4) . strstr ", " . strstr "_thread_id = " . shows (_ContextThreadId ctx) . nl
    , pindent (space + 4) . strstr "}" . nl
    ]

showsCurrentState :: Set.Set LogicVar -> Context -> [Cell] -> Stack -> ShowS
showsCurrentState fvs ctx cells stack = strcat
    [ strstr "--------------------------------" . nl 
    , strstr "* The top of the current stack is:" . nl
    , showStackItem fvs 4 (ctx, cells) . nl
    , strstr "* The rest of the current stack is:" . nl
    , strcat
        [ strcat
            [ pindent 0 . strstr "- (#" . shows i . strstr ")" . nl
            , showStackItem fvs 4 item . nl
            ]
        | (i, item) <- zip [1, 2 .. length stack] stack
        ]
    , strstr "--------------------------------" . nl
    ]

instantiateFact :: Fact -> ScopeLevel -> StateT Labeling (ExceptT KernelErr (UniqueT IO)) (TermNode, TermNode)
instantiateFact fact level
    = case unfoldlNApp (rewrite HNF fact) of
        (NCon (DC (DC_LO LO_ty_pi)), [fact1]) -> do
            uni <- getUnique
            let var = LV_ty_var uni
            modify (enrollLabel var level)
            instantiateFact (mkNApp fact1 (mkLVar var)) level
        (NCon (DC (DC_LO LO_pi)), [fact1]) -> do
            uni <- getUnique
            let var = LV_Unique uni
            modify (enrollLabel var level)
            instantiateFact (mkNApp fact1 (mkLVar var)) level
        (NCon (DC (DC_LO LO_if)), [conclusion, premise]) -> return (conclusion, premise)
        (NCon (DC (DC_LO logical_operator)), args) -> lift (throwE (BadFactGiven (foldlNApp (mkNCon logical_operator) args)))
        (t, ts) -> return (foldlNApp t ts, mkNCon LO_true)

runLogicalOperator :: LogicalOperator -> [TermNode] -> Context -> [Fact] -> ScopeLevel -> CallId -> [Cell] -> Stack -> ExceptT KernelErr (UniqueT IO) Stack
runLogicalOperator LO_true [] ctx facts level call_id cells stack = return ((ctx, cells) : stack)
runLogicalOperator LO_fail [] ctx facts level call_id cells stack = return stack
runLogicalOperator LO_debug [loc_str] ctx facts level call_id cells stack = runDebugger loc_str ctx facts level call_id cells stack
runLogicalOperator LO_cut [] ctx facts level call_id cells stack = return ((ctx, cells) : [ (ctx', cells') | (ctx', cells') <- stack, _ContextThreadId ctx' < call_id ])
runLogicalOperator LO_and [goal1, goal2] ctx facts level call_id cells stack = return ((ctx, mkCell facts level goal1 call_id : mkCell facts level goal2 call_id : cells) : stack)
runLogicalOperator LO_or [goal1, goal2] ctx facts level call_id cells stack = return ((ctx, mkCell facts level goal1 call_id : cells) : (ctx, mkCell facts level goal2 call_id : cells) : stack)
runLogicalOperator LO_imply [fact1, goal2] ctx facts level call_id cells stack = return ((ctx, mkCell (fact1 : facts) level goal2 call_id : cells) : stack)
runLogicalOperator LO_sigma [goal1] ctx facts level call_id cells stack = do
    uni <- getUnique
    let var = LV_Unique uni
    return ((ctx { _CurrentLabeling = enrollLabel var level (_CurrentLabeling ctx) }, mkCell facts level (mkNApp goal1 (mkLVar var)) call_id : cells) : stack)
runLogicalOperator LO_pi [goal1] ctx facts level call_id cells stack = do
    uni <- getUnique
    let con = DC (DC_Unique uni)
    return ((ctx { _CurrentLabeling = enrollLabel con (level + 1) (_CurrentLabeling ctx) }, mkCell facts (level + 1) (mkNApp goal1 (mkNCon con)) call_id : cells) : stack)
runLogicalOperator LO_is [lhs, rhs] ctx facts level call_id cells stack = execIs (ctx { _LeftConstraints = EvalutionConstraint lhs rhs : _LeftConstraints ctx }) cells stack
runLogicalOperator logical_operator args ctx facts level call_id cells stack = throwE (BadGoalGiven (foldlNApp (mkNCon logical_operator) args))

execIs :: MonadUnique m => Context -> [Cell] -> Stack -> m Stack
execIs ctx cells stack = case solveArithmetic (_LeftConstraints ctx) of
    Nothing -> return stack
    Just (theta, constraints)
        | Map.null (unVarBinding theta) -> return ((ctx { _LeftConstraints = constraints }, cells) : stack)
        | otherwise -> return (((zonkLVar theta ctx) { _LeftConstraints = constraints }, map (zonkLVar theta) cells) : stack)

solveArithmetic :: [Constraint] -> Maybe (VarBinding, [Constraint])
solveArithmetic = loop mempty . map normalize where
    normalize :: Constraint -> Constraint
    normalize (DisagreementConstraint eqn) = DisagreementConstraint eqn
    normalize (EvalutionConstraint lhs rhs) = EvalutionConstraint (rewrite NF lhs) (rewrite NF rhs)
    normalize (ArithmeticConstraint arith) = ArithmeticConstraint (rewrite NF arith)
    loop :: VarBinding -> [Constraint] -> Maybe (VarBinding, [Constraint])
    loop theta constraints = case [ VarBinding (Map.singleton x (mkNCon (DC_NatL v))) | EvalutionConstraint (LVar x) rhs <- constraints, Right v <- [evaluateA rhs] ] of
        theta' : _ -> loop (theta' <> theta) (map normalize (zonkLVar theta' constraints))
        [] -> fmap (\constraints' -> (theta, concat constraints')) (mapM check constraints)
    check :: Constraint -> Maybe [Constraint]
    check (DisagreementConstraint eqn) = Just [DisagreementConstraint eqn]
    check (EvalutionConstraint lhs rhs) = case (evaluateA lhs, evaluateA rhs) of
        (Left "ill", _) -> Nothing
        (_, Left "ill") -> Nothing
        (Right v1, Right v2) -> if v1 == v2 then Just [] else Nothing
        _ -> Just [EvalutionConstraint lhs rhs]
    check (ArithmeticConstraint arith) = case evaluateB arith of
        Right okay -> if okay then Just [] else Nothing
        Left "non" -> Just [ArithmeticConstraint arith]
        Left _ -> Nothing

evaluateA :: TermNode -> Either ErrMsg Integer
evaluateA (NApp (NCon (DC DC_Succ)) t1) = do
    v1 <- evaluateA t1
    return (succ v1)
evaluateA (NApp (NApp (NCon (DC DC_plus)) t1) t2) = do
    v1 <- evaluateA t1
    v2 <- evaluateA t2
    return (v1 + v2)
evaluateA (NApp (NApp (NCon (DC DC_minus)) t1) t2) = do
    v1 <- evaluateA t1
    v2 <- evaluateA t2
    if v1 >= v2 then return (v1 - v2) else Left "ill"
evaluateA (NApp (NApp (NCon (DC DC_mul)) t1) t2) = do
    v1 <- evaluateA t1
    v2 <- evaluateA t2
    return (v1 * v2)
evaluateA (NApp (NApp (NCon (DC DC_div)) t1) t2) = do
    v1 <- evaluateA t1
    v2 <- evaluateA t2
    if v2 == 0 then Left "ill" else return (v1 `div` v2)
evaluateA t = case reads (shows t "") of
    [(v, "")] -> return v
    _ -> Left "non"

evaluateB :: TermNode -> Either ErrMsg Bool
evaluateB (NApp (NApp (NApp (NCon (DC DC_eq)) (NCon (TC (TC_Named "nat")))) t1) t2) = do
    v1 <- evaluateA t1
    v2 <- evaluateA t2
    return (v1 == v2)
evaluateB (NApp (NApp (NCon (DC DC_le)) t1) t2) = do
    v1 <- evaluateA t1
    v2 <- evaluateA t2
    return (v1 <= v2)
evaluateB (NApp (NApp (NCon (DC DC_lt)) t1) t2) = do
    v1 <- evaluateA t1
    v2 <- evaluateA t2
    return (v1 < v2)
evaluateB (NApp (NApp (NCon (DC DC_ge)) t1) t2) = do
    v1 <- evaluateA t1
    v2 <- evaluateA t2
    return (v1 >= v2)
evaluateB (NApp (NApp (NCon (DC DC_gt)) t1) t2) = do
    v1 <- evaluateA t1
    v2 <- evaluateA t2
    return (v1 > v2)
evaluateB _ = Left "non"

runDebugger :: TermNode -> Context -> [Fact] -> ScopeLevel -> CallId -> [Cell] -> Stack -> ExceptT KernelErr (UniqueT IO) Stack
runDebugger loc_str ctx facts level call_id cells stack = do
    liftIO $ writeIORef (_debuggindModeOn ctx) True
    liftIO $ putStrLn ("*** debugger called with " ++ shows loc_str "")
    return ((ctx, cells) : stack)

runTransition :: RuntimeEnv -> Set.Set LogicVar -> Stack -> ExceptT KernelErr (UniqueT IO) Satisfied
runTransition env free_lvars = go where
    failure :: ExceptT KernelErr (UniqueT IO) Stack
    failure = return []
    success :: (Context, [Cell]) -> ExceptT KernelErr (UniqueT IO) Stack
    success with = return [with]
    search :: [Fact] -> ScopeLevel -> Constant -> [TermNode] -> Context -> [Cell] -> ExceptT KernelErr (UniqueT IO) Stack
    search facts level predicate args ctx cells = do
        call_id <- getUnique
        ans1 <- if predicate `elem` [DC DC_ge, DC DC_gt, DC DC_le, DC DC_lt] then execIs (ctx { _LeftConstraints = ArithmeticConstraint (foldlNApp (NCon predicate) args) : _LeftConstraints ctx }) cells [] else failure
        ans2 <- fmap concat $ forM facts $ \fact -> do
            ((goal', new_goal), labeling) <- runStateT (instantiateFact fact level) (_CurrentLabeling ctx)
            case unfoldlNApp (rewrite HNF goal') of
                (NCon predicate', args')
                    | predicate == predicate' -> do
                        hopu_output <- if length args == length args' then lift (runHOPU labeling (zipWith (:=?=:) args args' ++ [ eqn | DisagreementConstraint eqn <- _LeftConstraints ctx ])) else throwE (BadFactGiven goal')
                        let new_level = level
                            new_facts = facts
                        case hopu_output of
                            Nothing -> failure
                            Just (new_disagreements, HopuSol new_labeling subst) -> do
                                let old_constraints = zonkLVar subst (_LeftConstraints ctx)
                                case solveArithmetic (map DisagreementConstraint new_disagreements ++ [ EvalutionConstraint lhs rhs | EvalutionConstraint lhs rhs <- old_constraints ] ++ [ ArithmeticConstraint arith | ArithmeticConstraint arith <- old_constraints ]) of
                                    Nothing -> failure
                                    Just (theta, new_constraints) -> do
                                        let subst' = if Map.null (unVarBinding theta) then subst else theta <> subst
                                        success
                                            ( Context
                                                { _TotalVarBinding = zonkLVar subst' (_TotalVarBinding ctx)
                                                , _CurrentLabeling = new_labeling
                                                , _LeftConstraints = new_constraints
                                                , _ContextThreadId = call_id
                                                , _debuggindModeOn = _debuggindModeOn ctx
                                                }
                                            , zonkLVar subst' (mkCell new_facts new_level new_goal call_id : cells)
                                            )
                _ -> failure
        return (ans1 ++ ans2)
    dispatch :: Context -> [Fact] -> ScopeLevel -> (TermNode, [TermNode]) -> CallId -> [Cell] -> Stack -> ExceptT KernelErr (UniqueT IO) Satisfied
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
    go :: Stack -> ExceptT KernelErr (UniqueT IO) Satisfied
    go [] = return False
    go ((ctx, cells) : stack) = do
        keep_going <- liftIO (_PutStr env ctx (showsCurrentState free_lvars ctx cells stack ""))
        unless keep_going (throwE QuitRequested)
        case cells of
            [] -> do
                want_more <- liftIO (_Answer env ctx)
                if want_more then go stack else return True
            Cell facts level goal call_id : cells -> dispatch ctx facts level (unfoldlNApp (rewrite HNF goal)) call_id cells stack
