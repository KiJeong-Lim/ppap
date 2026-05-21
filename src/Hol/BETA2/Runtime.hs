{-# LANGUAGE ScopedTypeVariables #-}
module Hol.BETA2.Runtime where

import Calc.Presburger.Internal
import Hol.BETA2.Arith
import Hol.BETA2.Debugger
import Hol.BETA2.Notation (NotationDB)
import qualified Hol.BETA2.Notation as Notation
import Hol.BETA2.TermNode
import Hol.BETA2.HOPU
import Hol.BETA2.Constant
import Hol.BETA2.Header
import Control.Monad
import Control.Monad.IO.Class
import Control.Monad.Trans.Class
import Control.Monad.Trans.Except
import Control.Monad.Trans.Reader
import Control.Monad.Trans.State.Strict
import Data.IORef
import Data.Maybe
import qualified Data.IntMap.Strict as IntMap
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

data KernelErr
    = BadGoalGiven TermNode
    | BadFactGiven TermNode
    | UnsupportedArithmeticConstraint TermNode
    deriving ()

data Constraint
    = DisagreementConstraint Disagreement
    | EvalutionConstraint TermNode TermNode
    | ArithmeticConstraint !(TermNode)
    deriving (Eq, Ord)

data Cell
    = Cell
        { _GivenFacts :: Map.Map Constant [Fact]
        , _GivenHypos :: [Fact]
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
        { _PutStr :: RuntimeEnv -> Context -> String -> IO ()
        , _Answer :: Context -> IO RunMore
        , _PrintPrimitive :: Context -> TermNode -> IO ()
        , _ReadPrimitive :: Context -> TermNode -> IO (Maybe TermNode)
        , _TypeInfo :: Map.Map LogicVar (MonoType Int)
        , _PendingSubst :: IORef LogicVarSubst
        , _ProgramTypeEnv :: TypeEnv
        , _VerboseTyping :: IORef Bool
        , _StackRef :: IORef Stack
        , _NameCacheRef :: IORef NameCache
        , _DebuggingRef :: IORef Debugging
        , _NotationDB :: NotationDB
        , _ModuleName :: String
        }
    deriving ()

newtype Runtime a = Runtime { unRuntime :: ReaderT RuntimeEnv IO a }

instance Functor Runtime where
    fmap f (Runtime m) = Runtime (fmap f m)

instance Applicative Runtime where
    pure = Runtime . pure
    Runtime f <*> Runtime x = Runtime (f <*> x)

instance Monad Runtime where
    return = pure
    Runtime m >>= k = Runtime (m >>= unRuntime . k)

instance MonadIO Runtime where
    liftIO = Runtime . liftIO

runRuntime :: Runtime a -> RuntimeEnv -> IO a
runRuntime (Runtime m) = runReaderT m

askRuntimeEnv :: Runtime RuntimeEnv
askRuntimeEnv = Runtime ask

data Snapshot
    = Snapshot
        { _SnapStack :: Stack
        , _SnapPendingSubst :: LogicVarSubst
        , _SnapNameCache :: NameCache
        }

snapshot :: Runtime Snapshot
snapshot = do
    env <- askRuntimeEnv
    liftIO $ do
        st <- readIORef (_StackRef env)
        ps <- readIORef (_PendingSubst env)
        nc <- readIORef (_NameCacheRef env)
        return (Snapshot { _SnapStack = st, _SnapPendingSubst = ps, _SnapNameCache = nc })

restore :: Snapshot -> Runtime ()
restore snap = do
    env <- askRuntimeEnv
    liftIO $ do
        writeIORef (_StackRef env) (_SnapStack snap)
        writeIORef (_PendingSubst env) (_SnapPendingSubst snap)
        currentCache <- readIORef (_NameCacheRef env)
        writeIORef (_NameCacheRef env) (mergeKeepingNewEntries (_SnapNameCache snap) currentCache)

cmdDebugToggle :: Runtime ()
cmdDebugToggle = do
    env <- askRuntimeEnv
    liftIO $ modifyIORef (_DebuggingRef env) not

cmdQuit :: Runtime ()
cmdQuit = do
    env <- askRuntimeEnv
    liftIO $ do
        writeIORef (_StackRef env) []
        writeIORef (_PendingSubst env) (VarBinding Map.empty)

cmdShow :: SmallId -> Runtime String
cmdShow name = do
    env <- askRuntimeEnv
    liftIO $ do
        st <- readIORef (_StackRef env)
        cache <- readIORef (_NameCacheRef env)
        let resolved = case fromDisplay name cache of
                Just lv -> Just lv
                Nothing -> parseAnonymousLV name
        case (st, resolved) of
            (_, Nothing) -> return ("unknown variable '?" ++ name ++ "'")
            ([], _) -> return "no active goal"
            ((ctx, _) : _, Just lv) ->
                case Map.lookup lv (unVarBinding (_TotalVarBinding ctx)) of
                    Nothing -> return "unbound"
                    Just t -> return (prettyTerm (_NotationDB env) cache t "")

scopeEscaping :: Labeling -> ScopeLevel -> LogicVar -> TermNode -> ([Constant], [LogicVar])
scopeEscaping labeling targetScope targetLV = walk where
    walk :: TermNode -> ([Constant], [LogicVar])
    walk (LVar v)
        | v == targetLV = ([], [])
        | lookupLabel v labeling > targetScope = ([], [v])
        | otherwise = ([], [])
    walk (NCon c _)
        | lookupLabel c labeling > targetScope = ([c], [])
        | otherwise = ([], [])
    walk (NApp t1 t2 _) = combine (walk t1) (walk t2)
    walk (NLam _ _ t _) = walk t
    walk (Susp body _ _ _) = walk body
    walk _ = ([], [])
    combine (a1, b1) (a2, b2) = (a1 ++ a2, b1 ++ b2)

cmdAssign :: SmallId -> TermNode -> Runtime (Either ErrMsg ())
cmdAssign name term = do
    snap <- snapshot
    env <- askRuntimeEnv
    outcome <- liftIO $ do
        st <- readIORef (_StackRef env)
        cache <- readIORef (_NameCacheRef env)
        case st of
            [] -> return (Left "no active goal")
            (ctx, _) : _ -> do
                let targetLV = case fromDisplay name cache of
                        Just lv -> lv
                        Nothing -> fromMaybe (LV_Named name) (parseAnonymousLV name)
                existingPending <- readIORef (_PendingSubst env)
                let composed_subst = existingPending <> _TotalVarBinding ctx
                    t_zonked = bindVars composed_subst term
                if targetLV `Set.member` getLVars t_zonked
                    then return (Left ("occurs check failed for '" ++ name ++ "'"))
                    else do
                        let labeling = _CurrentLabeling ctx
                            scope_target = case targetLV of
                                LV_Named _ -> 0
                                _ -> lookupLabel targetLV labeling
                            (escapedCons, escapedVars) = scopeEscaping labeling scope_target targetLV t_zonked
                        if not (null escapedCons) || not (null escapedVars)
                            then do
                                let renderCon c = shows c ""
                                    renderVar v = case v of
                                        LV_Unique _ (DispHint (Just s)) -> s
                                        LV_Unique u (DispHint Nothing) -> "?V_" ++ show (unUnique u)
                                        LV_ty_var u -> "?TV_" ++ show (unUnique u)
                                        LV_Named n -> n
                                    items = map renderCon escapedCons ++ map renderVar escapedVars
                                return (Left ("scope violation for '" ++ name ++ "' — out-of-scope: " ++ List.intercalate ", " items))
                            else do
                                let new_binding = VarBinding (Map.singleton targetLV t_zonked)
                                    composedAfter = new_binding <> existingPending <> _TotalVarBinding ctx
                                    arithTermsAfter =
                                        [ bindVars composedAfter t
                                        | ArithmeticConstraint t <- _LeftConstraints ctx
                                        ]
                                if isInconsistent arithTermsAfter
                                    then return (Left ("inconsistent with arithmetic constraints for '" ++ name ++ "'"))
                                    else do
                                        writeIORef (_PendingSubst env) (new_binding <> existingPending)
                                        return (Right ())
    case outcome of
        Left err -> do
            restore snap
            return (Left err)
        Right () -> return (Right ())

instance ZonkLVar Context where
    zonkLVar theta ctx = Context
        { _TotalVarBinding = theta <> _TotalVarBinding ctx
        , _CurrentLabeling = zonkLVar theta (_CurrentLabeling ctx)
        , _LeftConstraints = zonkLVar theta (_LeftConstraints ctx)
        , _ContextThreadId = _ContextThreadId ctx
        , _debuggindModeOn = _debuggindModeOn ctx
        }

instance ZonkLVar Constraint where
    zonkLVar theta (DisagreementConstraint eqn)
        = DisagreementConstraint (bindVars theta eqn)
    zonkLVar theta (EvalutionConstraint lhs rhs)
        | LVar x <- lhs = case Map.lookup x (unVarBinding theta) of
            Nothing -> EvalutionConstraint lhs (bindVars theta rhs)
            Just t -> ArithmeticConstraint (mkNApp (mkNApp (mkNApp (mkNCon (DC DC_eq)) (mkNCon (TC (TC_Named "nat")))) t) (bindVars theta rhs))
        | otherwise = EvalutionConstraint (bindVars theta lhs) (bindVars theta rhs)
    zonkLVar theta (ArithmeticConstraint arith)
        = ArithmeticConstraint (bindVars theta arith)

instance ZonkLVar Cell where
    zonkLVar theta (Cell facts hyps level goal call_id) = mkCell facts (bindVars theta hyps) level (bindVars theta goal) call_id

instance Show Constraint where
    showsPrec prec (DisagreementConstraint eqn) = showsPrec prec eqn
    showsPrec prec (EvalutionConstraint lhs rhs) = showsPrec prec lhs . strstr " is " . showsPrec prec rhs
    showsPrec prec (ArithmeticConstraint arith) = showsPrec prec arith

mkCell :: Map.Map Constant [Fact] -> [Fact] -> ScopeLevel -> Goal -> CallId -> Cell
mkCell facts hyps level goal call_id = goal `seq` Cell { _GivenFacts = facts, _GivenHypos = hyps, _ScopeLevel = level, _WantedGoal = goal, _CellCallId = call_id }

showsvdash :: Show goal => Indentation -> [Fact] -> goal -> ShowS
showsvdash space [] goal = strstr "|- " . shows goal
showsvdash space [hyp] goal = shows hyp . strstr " |- " . shows goal
showsvdash space (hyp : hyps) goal = shows hyp . strstr ", " . showsvdash space hyps goal

showsMonoType :: NotationDB -> Int -> MonoType Int -> ShowS
showsMonoType db prec t = case Notation.tryFoldType db t of
    Just (name, []) -> strstr name
    Just (name, args) ->
        let inner = strstr name . List.foldr (.) id [ strstr " " . showsMonoType db 7 a | a <- args ]
        in if prec > 6 then strstr "(" . inner . strstr ")" else inner
    Nothing -> showsMonoTypeRaw db prec t

showsMonoTypeRaw :: NotationDB -> Int -> MonoType Int -> ShowS
showsMonoTypeRaw _  _    (TyVar i) = strstr "a_" . shows i
showsMonoTypeRaw _  _    (TyMTV mtv) = strstr "?t" . shows mtv
showsMonoTypeRaw _  _    (TyCon (TCon (TC_Unique uni) _)) = strstr "?TV_" . shows (unUnique uni)
showsMonoTypeRaw _  _    (TyCon (TCon tc _)) = shows tc
showsMonoTypeRaw db prec (TyApp (TyApp (TyCon (TCon TC_Arrow _)) t1) t2) =
    let inner = showsMonoType db 5 t1 . strstr " -> " . showsMonoType db 4 t2
    in if prec > 4 then strstr "(" . inner . strstr ")" else inner
showsMonoTypeRaw db prec (TyApp t1 t2) =
    let inner = showsMonoType db 6 t1 . strstr " " . showsMonoType db 7 t2
    in if prec > 6 then strstr "(" . inner . strstr ")" else inner

showLVarVN :: LogicVar -> ShowS
showLVarVN (LV_ty_var uni) = strstr "?TV_" . shows (unUnique uni)
showLVarVN (LV_Unique uni (DispHint (Just s))) = strstr s
showLVarVN (LV_Unique uni (DispHint Nothing)) = strstr "?V_" . shows (unUnique uni)
showLVarVN (LV_Named name) = strstr name

showsMonoTypeIn :: NotationDB -> Bool -> Labeling -> LogicVar -> Maybe (MonoType Int) -> ShowS
showsMonoTypeIn db False _ _ mtyp = case mtyp of
    Just t -> showsMonoType db 0 t
    Nothing -> strstr "?"
showsMonoTypeIn db True labeling lv mtyp = render lv mtyp where
    render :: LogicVar -> Maybe (MonoType Int) -> ShowS
    render lv mtyp =
        let (scope_v, myK) = case lv of
                LV_Named _ -> (-1, -1)
                _ -> (lookupLabel lv labeling, lvKey lv)
            cons = [ renderCon uni cTyp
                   | (uni, cTyp) <- IntMap.toAscList (_ConTypes labeling)
                   , IntMap.findWithDefault maxBound uni (_ConLabel labeling) <= scope_v
                   ]
            vars = [ renderVar uni
                   | (uni, scp) <- IntMap.toAscList (_VarLabel labeling)
                   , uni < myK
                   , scp <= scope_v
                   ]
            entries = cons ++ vars
            prefix = case entries of
                [] -> strstr "("
                _ -> strstr "(" . sepBy (strstr ", ") entries . strstr " "
            renderedTy = case mtyp of
                Just t -> showsMonoType db 0 t
                Nothing -> strstr "?"
        in prefix . strstr "|- " . renderedTy . strstr ")"
    renderCon :: Int -> MonoType Int -> ShowS
    renderCon uni cTyp = strstr "c_" . shows uni . strstr " : " . showsMonoType db 0 cTyp
    renderVar :: Int -> ShowS
    renderVar uni
        | IntMap.member uni (_TyVarKeys labeling) = strstr "?TV_" . shows uni
        | otherwise =
            let innerLV = LV_Unique (Unique uni) noHint
                mInnerTy = IntMap.lookup uni (_VarTypes labeling)
            in strstr "?V_" . shows uni . strstr " : " . render innerLV mInnerTy
    sepBy :: ShowS -> [ShowS] -> ShowS
    sepBy _ [] = id
    sepBy _ [x] = x
    sepBy sep (x : xs) = x . sep . sepBy sep xs

showStackItem :: String -> NotationDB -> Bool -> Set.Set LogicVar -> Map.Map LogicVar (MonoType Int) -> Indentation -> (Context, [Cell]) -> ShowS
showStackItem mname db verbose fvs typeMap space (ctx, cells) = strcat
    [ pindent space . strstr "+ progressings = " . plist (space + 4) [ strstr "?- [ " . showsvdash (space + 8) hyps goal . strstr " ] # call_id = " . shows call_id | Cell facts hyps level goal call_id <- cells ] . nl
    , pindent space . strstr "+ context = Context" . nl
    , pindent (space + 4) . strstr "{ " . strstr "_substitution = " . plist (space + 8) [ shows (LVar v) . strstr " := " . shows t | (v, t) <- Map.toList (unVarBinding (_TotalVarBinding ctx)), v `Set.member` fvs ] . nl
    , pindent (space + 4) . strstr ", " . strstr "_constraints = " . plist (space + 8) [ shows constraint | constraint <- _LeftConstraints ctx ] . nl
    , pindent (space + 4) . strstr ", " . strstr "_typing = " . plist (space + 8) (concat
        [
        [ showLVarVN v . strstr " : " . showsMonoTypeIn db verbose (_CurrentLabeling ctx) v (Just typ)
        | (v, typ) <- Map.toList typeMap, v `Set.member` fvs
        ]
        ,
        [ showLVarVN v . strstr " : " . showsMonoTypeIn db verbose (_CurrentLabeling ctx) v (lookupLVarType v (_CurrentLabeling ctx))
        | (uni, _) <- IntMap.toList (_VarLabel (_CurrentLabeling ctx))
        , not (IntMap.member uni (_TyVarKeys (_CurrentLabeling ctx)))
        , let v = LV_Unique (Unique uni) noHint
        ]
        ]
      ) . nl
    , pindent (space + 4) . strstr ", " . strstr "_thread_id = " . shows (_ContextThreadId ctx) . nl
    , pindent (space + 4) . strstr ", " . strstr "_sloc = " . slocLine cells . nl
    , pindent (space + 4) . strstr "}" . nl
    ]
  where
    slocLine :: [Cell] -> ShowS
    slocLine [] = strstr "(none)"
    slocLine (cell : _) = case getNodeSLoc (_WantedGoal cell) of
        Just l  -> strstr "`" . pprintMSLoc (Just mname) l . strstr "'"
        Nothing -> strstr "(none)"

showsCurrentState :: String -> NotationDB -> Bool -> Set.Set LogicVar -> Map.Map LogicVar (MonoType Int) -> Context -> [Cell] -> Stack -> ShowS
showsCurrentState mname db verbose fvs typeMap ctx cells stack = strcat
    [ strstr "--------------------------------" . nl
    , strstr "* The top of the current stack is:" . nl
    , showStackItem mname db verbose fvs typeMap 4 (ctx, cells) . nl
    , strstr "* The rest of the current stack is:" . nl
    , strcat
        [ strcat
            [ pindent 0 . strstr "- (#" . shows i . strstr ")" . nl
            , showStackItem mname db verbose fvs typeMap 4 item . nl
            ]
        | (i, item) <- zip [1, 2 .. length stack] stack
        ]
    , strstr "--------------------------------" . nl
    ]

instantiateFact :: UniqueM m => Fact -> ScopeLevel -> StateT Labeling (ExceptT KernelErr m) (TermNode, TermNode)
instantiateFact fact level
    = case unfoldlNApp (rewrite HNF fact) of
        (NCon (DC (DC_LO LO_ty_pi)) _, [fact1]) -> do
            uni <- getUnique
            let var = LV_ty_var uni
                mtvKey = case rewrite HNF fact1 of
                    NLam _ (LamType (Just (TyMTV mtv))) _ _ -> Just mtv
                    _ -> Nothing
                fact1' = case mtvKey of
                    Just mtv -> substTyMTV mtv uni fact1
                    Nothing -> fact1
            modify (enrollLabel var level)
            modify (\lbl -> lbl { _TyVarKeys = IntMap.insert (unUnique uni) () (_TyVarKeys lbl) })
            instantiateFact (mkNApp fact1' (mkLVar var)) level
        (NCon (DC (DC_LO LO_pi)) _, [fact1]) -> do
            uni <- getUnique
            let (mhint, mty) = case rewrite HNF fact1 of
                    NLam h ty _ _ -> (h, unLamType ty)
                    _ -> (Nothing, Nothing)
                var = LV_Unique uni (mkHint mhint)
            modify (enrollLabel var level)
            case mty of
                Just ty -> modify (\lbl -> lbl { _VarTypes = IntMap.insert (unUnique uni) ty (_VarTypes lbl) })
                Nothing -> return ()
            instantiateFact (mkNApp fact1 (mkLVar var)) level
        (NCon (DC (DC_LO LO_if)) _, [conclusion, premise]) -> return (conclusion, premise)
        (NCon (DC (DC_LO logical_operator)) _, args) -> lift (throwE (BadFactGiven (foldlNApp (mkNCon logical_operator) args)))
        (t, ts) -> return (foldlNApp t ts, mkNCon LO_true)

runLogicalOperator :: UniqueM m => LogicalOperator -> [TermNode] -> Context -> Map.Map Constant [Fact] -> [Fact] -> ScopeLevel -> CallId -> [Cell] -> Stack -> ExceptT KernelErr m Stack
runLogicalOperator LO_true [] ctx facts hyps level call_id cells stack
    = return ((ctx, cells) : stack)
runLogicalOperator LO_fail [] ctx facts hyps level call_id cells stack
    = return stack
runLogicalOperator LO_debug [loc_str] ctx facts hyps level call_id cells stack
    = runDebugger loc_str ctx facts hyps level call_id cells stack
runLogicalOperator LO_cut [] ctx facts hyps level call_id cells stack
    = return ((ctx, cells) : [ (ctx', cells') | (ctx', cells') <- stack, _ContextThreadId ctx' < call_id ])
runLogicalOperator LO_and [goal1, goal2] ctx facts hyps level call_id cells stack
    = return ((ctx, mkCell facts hyps level goal1 call_id : mkCell facts hyps level goal2 call_id : cells) : stack)
runLogicalOperator LO_or [goal1, goal2] ctx facts hyps level call_id cells stack
    = return ((ctx, mkCell facts hyps level goal1 call_id : cells) : (ctx, mkCell facts hyps level goal2 call_id : cells) : stack)
runLogicalOperator LO_imply [fact1, goal2] ctx facts hyps level call_id cells stack
    = return ((ctx, mkCell facts (expandAssumptions fact1 ++ hyps) level goal2 call_id : cells) : stack)
runLogicalOperator LO_sigma [goal1] ctx facts hyps level call_id cells stack
    = do
        uni <- getUnique
        let (mhint, mty) = case rewrite HNF goal1 of
                NLam h ty _ _ -> (h, unLamType ty)
                _ -> (Nothing, Nothing)
            var = LV_Unique uni (mkHint mhint)
            labeling0 = enrollLabel var level (_CurrentLabeling ctx)
            labeling1 = case mty of
                Just ty -> labeling0 { _VarTypes = IntMap.insert (unUnique uni) ty (_VarTypes labeling0) }
                Nothing -> labeling0
        return ((ctx { _CurrentLabeling = labeling1 }, mkCell facts hyps level (mkNApp goal1 (mkLVar var)) call_id : cells) : stack)
runLogicalOperator LO_pi [goal1] ctx facts hyps level call_id cells stack
    = do
        uni <- getUnique
        let (mhint, mty) = case rewrite HNF goal1 of
                NLam h ty _ _ -> (h, unLamType ty)
                _ -> (Nothing, Nothing)
            con = DC (DC_Unique uni (mkHint mhint))
            labeling0 = enrollLabel con (level + 1) (_CurrentLabeling ctx)
            labeling1 = case mty of
                Just ty -> labeling0 { _ConTypes = IntMap.insert (unUnique uni) ty (_ConTypes labeling0) }
                Nothing -> labeling0
        return ((ctx { _CurrentLabeling = labeling1 }, mkCell facts hyps (level + 1) (mkNApp goal1 (mkNCon con)) call_id : cells) : stack)
runLogicalOperator LO_is [lhs, rhs] ctx facts hyps level call_id cells stack
    | Left "ill" == rhsValue
    = return stack
    | LVar x <- rewrite NF lhs
    , Right v <- rhsValue
    = bindIs x (mkNCon (DC (DC_NatL v)))
    | Right v <- rhsValue
    , Right lhs_v <- lhsValue
    = if lhs_v == v then return ((ctx, cells) : stack) else return stack
    | LVar x <- lhs'
    , Just rhs_s <- simplifyArithmetic rhs'
    , canBindIs x rhs_s
    = bindIs x rhs_s
    | ArithEqTrue <- arithmeticEquality lhs' rhs'
    = return ((ctx, cells) : stack)
    | ArithEqFalse <- arithmeticEquality lhs' rhs'
    = return stack
    | otherwise
    = return ((ctx { _LeftConstraints = EvalutionConstraint lhs' rhs' : _LeftConstraints ctx }, cells) : stack)
    where
        lhs' = rewrite NF lhs
        rhs' = rewrite NF rhs
        lhsValue = evaluateA lhs'
        rhsValue = evaluateA rhs'
        bindIs x rhs_s
            = execIs (zonkLVar theta ctx) (map (zonkLVar theta) cells) stack
            where
                theta = VarBinding (Map.singleton x rhs_s)
        canBindIs x t =
            x `Set.notMember` getLVars t && null badCons && null badVars
            where
                targetScope = lookupLabel x (_CurrentLabeling ctx)
                (badCons, badVars) = scopeEscaping (_CurrentLabeling ctx) targetScope x t
runLogicalOperator logical_operator args ctx facts hyps level call_id cells stack
    = throwE (BadGoalGiven (foldlNApp (mkNCon logical_operator) args))

expandAssumptions :: Fact -> [Fact]
expandAssumptions fact = case unfoldlNApp (rewrite HNF fact) of
    (NCon (DC (DC_LO LO_and)) _, [fact1, fact2]) -> expandAssumptions fact1 ++ expandAssumptions fact2
    (NCon (DC (DC_LO LO_if)) _, [conclusion, premise]) ->
        [ foldlNApp (mkNCon LO_if) [conclusion', premise]
        | conclusion' <- expandAssumptions conclusion
        ]
    (NCon (DC (DC_LO LO_pi)) _, [NLam mhint lam_ty body loc]) ->
        [ mkNApp (mkNCon LO_pi) (NLam mhint lam_ty body' loc)
        | body' <- expandAssumptions body
        ]
    (NCon (DC (DC_LO LO_ty_pi)) _, [NLam mhint lam_ty body loc]) ->
        [ mkNApp (mkNCon LO_ty_pi) (NLam mhint lam_ty body' loc)
        | body' <- expandAssumptions body
        ]
    _ -> [fact]

execIs :: MonadUnique m => Context -> [Cell] -> Stack -> m Stack
execIs ctx cells stack
    | isInconsistent new_arithmetic_constraints = return stack
    | otherwise = return ((ctx { _LeftConstraints = map DisagreementConstraint new_disagreements ++ map (uncurry EvalutionConstraint) new_evaluation_constraints ++ [ ArithmeticConstraint arith | arith <- new_arithmetic_constraints, evaluateB arith == Left "non" ] }, cells) : stack)
    where
        new_disagreements = [ eqn | DisagreementConstraint eqn <- _LeftConstraints ctx ]
        new_evaluation_constraints = [ (rewrite NF lhs, rewrite NF rhs) | EvalutionConstraint lhs rhs <- _LeftConstraints ctx ]
        new_arithmetic_constraints = [ rewrite NF arith | ArithmeticConstraint arith <- _LeftConstraints ctx ]

evaluateA :: TermNode -> Either ErrMsg Integer
evaluateA (NApp (NCon (DC DC_Succ) _) t1 _) = do
    v1 <- evaluateA t1
    return (succ v1)
evaluateA (NApp (NApp (NCon (DC DC_plus) _) t1 _) t2 _) = do
    v1 <- evaluateA t1
    v2 <- evaluateA t2
    return (v1 + v2)
evaluateA (NApp (NApp (NCon (DC DC_minus) _) t1 _) t2 _) = do
    v1 <- evaluateA t1
    v2 <- evaluateA t2
    if v1 >= v2 then return (v1 - v2) else Left "ill"
evaluateA (NApp (NApp (NCon (DC DC_mul) _) t1 _) t2 _) = do
    v1 <- evaluateA t1
    v2 <- evaluateA t2
    return (v1 * v2)
evaluateA (NApp (NApp (NCon (DC DC_div) _) t1 _) t2 _) = do
    v1 <- evaluateA t1
    v2 <- evaluateA t2
    if v2 == 0 then Left "ill" else return (v1 `div` v2)
evaluateA t = case reads (shows t "") of
    [(v, "")] -> return v
    _ -> Left "non"

evaluateB :: TermNode -> Either ErrMsg Bool
evaluateB (NApp (NApp (NApp (NCon (DC DC_eq) _) (NCon (TC (TC_Named "nat")) _) _) t1 _) t2 _) =
    case arithmeticEquality t1 t2 of
        ArithEqTrue -> Right True
        ArithEqFalse -> Right False
        ArithEqUnknown -> Left "non"
evaluateB (NApp (NApp (NCon (DC DC_le) _) t1 _) t2 _) = do
    v1 <- evaluateA t1
    v2 <- evaluateA t2
    return (v1 <= v2)
evaluateB (NApp (NApp (NCon (DC DC_lt) _) t1 _) t2 _) = do
    v1 <- evaluateA t1
    v2 <- evaluateA t2
    return (v1 < v2)
evaluateB (NApp (NApp (NCon (DC DC_ge) _) t1 _) t2 _) = do
    v1 <- evaluateA t1
    v2 <- evaluateA t2
    return (v1 >= v2)
evaluateB (NApp (NApp (NCon (DC DC_gt) _) t1 _) t2 _) = do
    v1 <- evaluateA t1
    v2 <- evaluateA t2
    return (v1 > v2)
evaluateB _ = Left "non"

data ArithmeticEquality
    = ArithEqTrue
    | ArithEqFalse
    | ArithEqUnknown
    deriving ()

arithmeticEquality :: TermNode -> TermNode -> ArithmeticEquality
arithmeticEquality t1 t2 =
    case (evaluateA t1', evaluateA t2') of
        (Right v1, Right v2) -> if v1 == v2 then ArithEqTrue else ArithEqFalse
        (Left "ill", _) -> ArithEqFalse
        (_, Left "ill") -> ArithEqFalse
        _ -> case (simplifyArithmetic t1', simplifyArithmetic t2') of
            (Just s1, Just s2) | rewrite NF s1 == rewrite NF s2 -> ArithEqTrue
            _ -> ArithEqUnknown
    where
        t1' = rewrite NF t1
        t2' = rewrite NF t2

mentionsArithmetic :: TermNode -> Bool
mentionsArithmetic t = case rewrite HNF t of
    NCon (DC (DC_NatL _)) _ -> False
    NCon (DC DC_Succ) _ -> True
    NCon (DC DC_plus) _ -> True
    NCon (DC DC_minus) _ -> True
    NCon (DC DC_mul) _ -> True
    NCon (DC DC_div) _ -> True
    NApp t1 t2 _ -> mentionsArithmetic t1 || mentionsArithmetic t2
    NLam _ _ body _ -> mentionsArithmetic body
    Susp body _ _ env -> mentionsArithmetic body || any mentionsSuspItem env
    _ -> False
  where
    mentionsSuspItem (Dummy _) = False
    mentionsSuspItem (Binds body _) = mentionsArithmetic body

simplifyArithmetic :: TermNode -> Maybe TermNode
simplifyArithmetic t = do
    (sawArithmetic, poly) <- Just (polyOf (rewrite NF t))
    if sawArithmetic then renderPoly (combinePoly poly) else Nothing
  where
    polyOf :: TermNode -> (Bool, [([TermNode], Integer)])
    polyOf (NCon (DC (DC_NatL n)) _) = (True, [([], n)])
    polyOf (NApp (NApp (NCon (DC DC_plus) _) t1 _) t2 _) =
        let (saw1, p1) = polyOf t1
            (saw2, p2) = polyOf t2
        in (saw1 || saw2 || True, p1 ++ p2)
    polyOf (NApp (NApp (NCon (DC DC_mul) _) t1 _) t2 _) =
        let (saw1, p1) = polyOf t1
            (saw2, p2) = polyOf t2
        in (saw1 || saw2 || True, multiplyPoly p1 p2)
    polyOf atom = (False, [([atom], 1)])
    multiplyPoly p1 p2 =
        [ (List.sort (factors1 ++ factors2), coeff1 * coeff2)
        | (factors1, coeff1) <- p1
        , (factors2, coeff2) <- p2
        ]
    combinePoly = foldl insertTerm [] where
        insertTerm [] term = [term]
        insertTerm ((factors, coeff) : rest) term@(factors', coeff')
            | factors == factors' =
                let coeff'' = coeff + coeff'
                in if coeff'' == 0 then rest else (factors, coeff'') : rest
            | otherwise = (factors, coeff) : insertTerm rest term
    renderPoly poly0 = case filter ((/= 0) . snd) poly0 of
        [] -> Just (mkNCon (DC_NatL 0))
        terms
            | all ((>= 0) . snd) terms -> Just (foldl1 add (map renderTerm terms))
            | otherwise -> Nothing
    renderTerm (factors, coeff) = case (coeff, factors) of
        (0, _) -> mkNCon (DC_NatL 0)
        (1, []) -> mkNCon (DC_NatL 1)
        (1, factor : rest) -> foldl mul factor rest
        (_, []) -> mkNCon (DC_NatL coeff)
        (_, _) -> foldl mul (mkNCon (DC_NatL coeff)) factors
    add t1 t2 = mkNApp (mkNApp (mkNCon DC_plus) t1) t2
    mul t1 t2 = mkNApp (mkNApp (mkNCon DC_mul) t1) t2

runDebugger :: UniqueM m => TermNode -> Context -> Map.Map Constant [Fact] -> [Fact] -> ScopeLevel -> CallId -> [Cell] -> Stack -> ExceptT KernelErr m Stack
runDebugger loc_str ctx facts hyps level call_id cells stack = do
    liftIO $ writeIORef (_debuggindModeOn ctx) True
    liftIO $ putStrLn ("*** debugger called with " ++ shows loc_str "")
    return ((ctx, cells) : stack)

runPresburger :: MyPresburgerFormulaRep -> Map.Map MyVar LogicVar -> Context -> [Cell] -> Stack -> Stack
runPresburger rep freeOf ctx cells stack =
    if entails compiledHyps compiledPhi
        then (ctx, cells) : stack
        else stack
  where
    theta :: LogicVar -> Maybe TermNode
    theta lv = case bindVars (_TotalVarBinding ctx) (LVar lv) of
        LVar lv' | lv == lv' -> Nothing
        t -> Just t
    repZonked :: MyPresburgerFormulaRep
    repZonked = zonkPresburger theta freeOf rep
    arithTerms :: [TermNode]
    arithTerms =
        [ bindVars (_TotalVarBinding ctx) t
        | ArithmeticConstraint t <- _LeftConstraints ctx
        ]
    liftedResults :: [LiftResult]
    liftedResults = mapMaybe liftConstraint arithTerms
    allLVs :: [LogicVar]
    allLVs = Set.toAscList $ Set.union
        (Set.fromList (Map.elems freeOf))
        (Set.unions [ Set.fromList (Map.elems (_freeOfLifted lr)) | lr <- liftedResults ])
    shared :: Map.Map LogicVar MyVar
    shared = Map.fromAscList (zip allLVs [theMinNumOfMyVar ..])
    phiRep :: MyPresburgerFormulaRep
    phiRep = renumberFormula shared freeOf repZonked
    hypReps :: [MyPresburgerFormulaRep]
    hypReps =
        [ renumberFormula shared (_freeOfLifted lr) (_liftedFormula lr)
        | lr <- liftedResults
        ]
    compiledPhi :: MyPresburgerFormula
    compiledPhi = fmap compilePresburgerTerm phiRep
    compiledHyps :: [MyPresburgerFormula]
    compiledHyps = map (fmap compilePresburgerTerm) hypReps

isInconsistent :: [TermNode] -> Bool
isInconsistent arithTerms
    | cheapKill = True
    | otherwise = entails compiledHyps (ValF False)
  where
    cheapKill :: Bool
    cheapKill = List.any
        (\t -> evaluateB t == Right False || evaluateB t == Left "ill")
        arithTerms
    liftedResults :: [LiftResult]
    liftedResults = mapMaybe liftConstraint arithTerms
    allLVs :: [LogicVar]
    allLVs = Set.toAscList $ Set.unions
        [ Set.fromList (Map.elems (_freeOfLifted lr)) | lr <- liftedResults ]
    shared :: Map.Map LogicVar MyVar
    shared = Map.fromAscList (zip allLVs [theMinNumOfMyVar ..])
    hypReps :: [MyPresburgerFormulaRep]
    hypReps =
        [ renumberFormula shared (_freeOfLifted lr) (_liftedFormula lr)
        | lr <- liftedResults
        ]
    compiledHyps :: [MyPresburgerFormula]
    compiledHyps = map (fmap compilePresburgerTerm) hypReps

runTransition :: forall m. UniqueM m => RuntimeEnv -> Set.Set LogicVar -> Stack -> ExceptT KernelErr m Satisfied
runTransition env free_lvars = go where
    failure :: ExceptT KernelErr m Stack
    failure = return []
    success :: (Context, [Cell]) -> ExceptT KernelErr m Stack
    success with = return [with]
    arithOpCheck :: CallId -> Context -> [Cell] -> Constant -> [Fact] -> (Integer -> Integer -> Bool) -> ExceptT KernelErr m Stack
    arithOpCheck call_id ctx cells predicate args op
        = case liftM2 op (evaluateA (args !! 0)) (evaluateA (args !! 1)) of
            Left "non" ->
                let candidate = foldlNApp (mkNConLoc Nothing predicate) args
                in case liftConstraint candidate of
                    Nothing -> throwE (UnsupportedArithmeticConstraint candidate)
                    Just _ ->
                        let newCtx = Context
                                { _TotalVarBinding = _TotalVarBinding ctx
                                , _CurrentLabeling = _CurrentLabeling ctx
                                , _LeftConstraints = ArithmeticConstraint candidate : _LeftConstraints ctx
                                , _ContextThreadId = call_id
                                , _debuggindModeOn = _debuggindModeOn ctx
                                }
                            arithTerms =
                                [ bindVars (_TotalVarBinding newCtx) t
                                | ArithmeticConstraint t <- _LeftConstraints newCtx
                                ]
                        in if isInconsistent arithTerms then failure else success (newCtx, cells)
            Right okay -> if okay then success (ctx, cells) else failure
            _ -> failure
    eqOpCheck :: Context -> [Cell] -> [TermNode] -> Maybe (ExceptT KernelErr m Stack)
    eqOpCheck ctx cells [_typeArg, lhs, rhs]
        | mentionsArithmetic lhs || mentionsArithmetic rhs = case arithmeticEquality (bindVars (_TotalVarBinding ctx) lhs) (bindVars (_TotalVarBinding ctx) rhs) of
            ArithEqTrue -> Just (success (ctx, cells))
            ArithEqFalse -> Just failure
            ArithEqUnknown -> Nothing
    eqOpCheck _ _ _ = Nothing
    primitivePrint :: Context -> [TermNode] -> [Cell] -> Stack -> ExceptT KernelErr m Stack
    primitivePrint ctx args cells stack | Just arg <- onePrimitiveArg args = do
        liftIO (_PrintPrimitive env ctx (bindVars (_TotalVarBinding ctx) arg))
        success (ctx, cells)
    primitivePrint _ args _ _ = throwE (BadGoalGiven (foldlNApp (mkNCon (DC_Named "print")) args))
    primitiveRead :: Context -> [TermNode] -> [Cell] -> Stack -> ExceptT KernelErr m Stack
    primitiveRead ctx args cells stack | Just arg <- onePrimitiveArg args = do
        mvalue <- liftIO (_ReadPrimitive env ctx arg)
        case mvalue of
            Nothing -> failure
            Just value -> case rewrite NF (bindVars (_TotalVarBinding ctx) arg) of
                LVar x
                    | canBindPrimitive x value ->
                        let theta = VarBinding (Map.singleton x value)
                        in execIs (zonkLVar theta ctx) (map (zonkLVar theta) cells) stack
                arg'
                    | rewrite NF arg' == rewrite NF value -> success (ctx, cells)
                _ -> failure
      where
        canBindPrimitive x t =
            x `Set.notMember` getLVars t
                && let targetScope = lookupLabel x (_CurrentLabeling ctx)
                       (badCons, badVars) = scopeEscaping (_CurrentLabeling ctx) targetScope x t
                   in null badCons && null badVars
    primitiveRead _ args _ _ = throwE (BadGoalGiven (foldlNApp (mkNCon (DC_Named "read")) args))
    onePrimitiveArg :: [TermNode] -> Maybe TermNode
    onePrimitiveArg [arg] = Just arg
    onePrimitiveArg [_typeArg, arg] = Just arg
    onePrimitiveArg _ = Nothing
    search :: Map.Map Constant [Fact] -> [Fact] -> ScopeLevel -> Constant -> [TermNode] -> Context -> [Cell] -> ExceptT KernelErr m Stack
    search facts hyps level predicate args ctx cells = do
        call_id <- getUnique
        let arithOpCheck' = arithOpCheck call_id ctx cells predicate args
        ans0 <- case predicate of
            DC DC_eq -> sequence (eqOpCheck ctx cells args)
            DC DC_ge -> Just <$> arithOpCheck' (>=)
            DC DC_gt -> Just <$> arithOpCheck' (>)
            DC DC_le -> Just <$> arithOpCheck' (<=)
            DC DC_lt -> Just <$> arithOpCheck' (<)
            _ -> return Nothing
        case ans0 of
            Just ans -> return ans
            Nothing -> searchFacts call_id
      where
        searchFacts call_id = do
            ans2 <- fmap concat (forM (Map.findWithDefault [] predicate facts) (matchFact call_id))
            ans3 <- fmap concat (forM hyps (matchFact call_id))
            return (ans2 ++ ans3)
        matchFact call_id fact = do
            ((goal', new_goal), labeling) <- runStateT (instantiateFact fact level) (_CurrentLabeling ctx)
            case unfoldlNApp (rewrite HNF goal') of
                (NCon predicate' _, args')
                    | predicate == predicate' -> do
                        hopu_output <- if length args == length args' then lift (runHOPU labeling (zipWith (:=?=:) args args' ++ [ eqn | DisagreementConstraint eqn <- _LeftConstraints ctx ])) else throwE (BadFactGiven goal')
                        let new_level = level
                            new_hyps = hyps
                        case hopu_output of
                            Nothing -> failure
                            Just (new_disagreements, HopuSol new_labeling subst) -> do
                                let new_evaluation_constraints = [ (rewrite NF lhs, rewrite NF rhs) | EvalutionConstraint lhs rhs <- zonkLVar subst (_LeftConstraints ctx) ]
                                    new_arithmetic_constraints = [ rewrite NF arith | ArithmeticConstraint arith <- zonkLVar subst (_LeftConstraints ctx) ]
                                if isInconsistent new_arithmetic_constraints then
                                    failure
                                else
                                    success
                                        ( Context
                                            { _TotalVarBinding = zonkLVar subst (_TotalVarBinding ctx)
                                            , _CurrentLabeling = new_labeling
                                            , _LeftConstraints = map DisagreementConstraint new_disagreements ++ [ EvalutionConstraint lhs rhs | (lhs, rhs) <- new_evaluation_constraints ] ++ [ ArithmeticConstraint arith | arith <- new_arithmetic_constraints, evaluateB (rewrite NF arith) == Left "non" ]
                                            , _ContextThreadId = call_id
                                            , _debuggindModeOn = _debuggindModeOn ctx
                                            }
                                        , zonkLVar subst (mkCell facts new_hyps new_level new_goal call_id : cells)
                                        )
                _ -> failure
    dispatch :: Context -> Map.Map Constant [Fact] -> [Fact] -> ScopeLevel -> (TermNode, [TermNode]) -> CallId -> [Cell] -> Stack -> ExceptT KernelErr m Satisfied
    dispatch ctx facts hyps level (NCon predicate _, args) call_id cells stack
        | DC (DC_LO logical_operator) <- predicate
        = do
            stack' <- runLogicalOperator logical_operator args ctx facts hyps level call_id cells stack
            go stack'
        | predicate == DC (DC_Named "print")
        = do
            stack' <- primitivePrint ctx args cells stack
            go stack'
        | predicate == DC (DC_Named "read")
        = do
            stack' <- primitiveRead ctx args cells stack
            go stack'
        | otherwise
        = do
            stack' <- search facts hyps level predicate args ctx cells
            go (stack' ++ stack)
    dispatch ctx _facts _hyps _level (NPresburgerCheck rep freeOf _, []) _call_id cells stack
        = go (runPresburger rep freeOf ctx cells stack)
    dispatch ctx facts hyps level (t, ts) call_id cells stack = throwE (BadGoalGiven (foldlNApp t ts))
    applyPending :: Stack -> ExceptT KernelErr m Stack
    applyPending [] = return []
    applyPending st@((ctx, cells) : rest) = liftIO $ do
        pending <- readIORef (_PendingSubst env)
        if Map.null (unVarBinding pending)
            then return st
            else do
                writeIORef (_PendingSubst env) (VarBinding Map.empty)
                let zonkFrame (c, cs) = (zonkLVar pending c, map (zonkLVar pending) cs)
                return (zonkFrame (ctx, cells) : map zonkFrame rest)
    go :: Stack -> ExceptT KernelErr m Satisfied
    go raw_stack = do
        stack0 <- applyPending raw_stack
        case stack0 of
            [] -> return False
            (ctx, cells) : stack -> do
                liftIO $ writeIORef (_StackRef env) ((ctx, cells) : stack)
                liftIO $ do
                    dbg <- readIORef (_debuggindModeOn ctx)
                    verbose <- readIORef (_VerboseTyping env)
                    when dbg $ _PutStr env env ctx (showsCurrentState (_ModuleName env) (_NotationDB env) verbose free_lvars (_TypeInfo env) ctx cells stack "")
                stackAfterCb <- liftIO (readIORef (_StackRef env))
                stack1 <- applyPending stackAfterCb
                case stack1 of
                    [] -> return False
                    (ctx', cells') : stack' -> case cells' of
                        [] -> do
                            want_more <- liftIO (_Answer env ctx')
                            if want_more then go stack' else return True
                        Cell facts hyps level goal call_id : rest_cells ->
                            dispatch ctx' facts hyps level (unfoldlNApp (rewrite HNF goal)) call_id rest_cells stack'

eraseTrivialBinding :: LogicVarSubst -> LogicVarSubst
eraseTrivialBinding = VarBinding . loop . unVarBinding where
    hasName :: LogicVar -> Bool
    hasName (LV_Named _) = True
    hasName _ = False
    loop :: Map.Map LogicVar TermNode -> Map.Map LogicVar TermNode
    loop = foldr go <*> Map.toAscList
    go :: (LogicVar, TermNode) -> Map.Map LogicVar TermNode -> Map.Map LogicVar TermNode
    go (v, t) = maybe id (dispatch v) (tryMatchLVar t)
    dispatch :: LogicVar -> LogicVar -> Map.Map LogicVar TermNode -> Map.Map LogicVar TermNode
    dispatch v1 v2
        | v1 == v2 = loop . Map.delete v1
        | not (hasName v1) = loop . Map.map (flatten (VarBinding { unVarBinding = Map.singleton v1 (LVar v2) })) . Map.delete v1
        | otherwise = id
    tryMatchLVar :: TermNode -> Maybe LogicVar
    tryMatchLVar t
        = case viewNestedNLam (rewrite NF t) of
            (n, t') -> case unfoldlNApp t' of
                (LVar v, ts) -> if ts == map mkNIdx [n - 1, n - 2 .. 0] then Just v else Nothing
                _ -> Nothing
