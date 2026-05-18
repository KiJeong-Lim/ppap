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
        -- §3.4: the debugger lists each user-visible flexible variable
        -- with its inferred `MonoType`. The map is keyed by `LogicVar`
        -- so the runtime can resolve a name shown at a breakpoint back
        -- to its type without dragging the type-check pipeline into
        -- `Runtime.hs`. It is set once per query (in `Main.mkRuntimeEnv`)
        -- and is read-only for the duration of the search.
        , _TypeInfo :: Map.Map LogicVar (MonoType Int)
        -- §3.2 `:assign`: the substitution accumulated by `:assign` between
        -- step boundaries. The REPL callback (`_PutStr`) writes a single
        -- `?V := t` binding into this IORef; the next entry to `go` reads
        -- it, applies `zonkLVar` to the entire stack (current `ctx`/cells
        -- plus every saved frame), and clears it. This decouples the IO
        -- callback (which has no `Stack` in scope) from the kernel loop
        -- that does. The IORef is created once per query in `Main`.
        , _PendingSubst :: IORef LogicVarSubst
        -- §3.4 CMTT: the program's declared-constant types, passed
        -- through to `Labeling._TypeEnv` at `execRuntime` start so
        -- HOPU's `typeOfTerm` can resolve `DC_Named`/`DC_LO`/etc.
        , _ProgramTypeEnv :: TypeEnv
        -- §3.4 CMTT: when `True`, `_typing` entries render with the full
        -- recursive CMTT context `(Γ |- τ)`. When `False` (default), only
        -- the type itself is shown. Toggled by `:verbose` at the debug
        -- prompt; the IORef is shared with the REPL so the next step
        -- reflects the new mode.
        , _VerboseTyping :: IORef Bool
        -- §4.4: the kernel's `go` loop publishes the live stack here
        -- before invoking the debug callback. `cmd*` functions read it
        -- to inspect the current state, and may write it to mutate the
        -- search frontier (e.g. `cmdQuit` empties it). The very next
        -- iteration of `go` reads back from this IORef.
        , _StackRef :: IORef Stack
        -- §4.4.4: the REPL's display-name cache. Lives in RuntimeEnv so
        -- that `cmd*` functions in the `Runtime` monad can update it
        -- (e.g. `cmdAssign` may introduce a new display name) without
        -- the REPL having to thread it manually.
        , _NameCacheRef :: IORef NameCache
        -- §4.4: a sibling reference to the same IORef stored as
        -- `Context._debuggindModeOn` in every Context. Kept on the env
        -- so that `cmdDebugToggle` works even when the goal stack is
        -- empty (post-`cmdQuit`, post-search-completion).
        , _DebuggingRef :: IORef Debugging
        -- §1.5 / §2.6: the program's notation database, built by the
        -- desugarer from the `infix*`/`prefix` declarations in the
        -- source file. Read by every viewer call so that user-defined
        -- fixity (and the built-in seed table) shows up in answer
        -- substitutions, `:show`/`:assign` output, and the residual
        -- constraint listing of §2.5.
        , _NotationDB :: NotationDB
        -- §3.2 module-aware diagnostics: the main module's path-derived
        -- (or header-declared) name, used to prefix every debug `_sloc`
        -- line with `[<mod>]`. Set once by `Main.mkRuntimeEnv` from
        -- `Program.moduleName`.
        , _ModuleName :: String
        }
    deriving ()

-- §4.4: Public Haskell API surface. Library callers (notably the
-- future `LoL`) invoke `cmd*` functions inside this monad rather
-- than fork-execing the REPL and scraping stdout. The single
-- reader environment carries every IORef the commands may touch.
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

-- §4.4.1: opaque transaction handle. Captures every piece of mutable
-- state the kernel uses to decide success/failure: the full goal
-- stack (which carries θ, C, the HOPU disagreement set as a subset
-- of C, and every saved frame), the pending substitution staged for
-- the next iteration, and the display-name cache at the moment of
-- the snapshot. `cmdAssign` calls `snapshot` before applying its
-- preconditions and `restore` if any of them fails.
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

-- §3.5 / §4.4.4 policy override: rollback restores the saved θ, C,
-- stack, and pending substitution, but does *not* discard cache
-- entries introduced *after* the snapshot was taken. The user's
-- display names should not jitter between two consecutive prompts
-- merely because the assignment that revealed a name failed.
restore :: Snapshot -> Runtime ()
restore snap = do
    env <- askRuntimeEnv
    liftIO $ do
        writeIORef (_StackRef env) (_SnapStack snap)
        writeIORef (_PendingSubst env) (_SnapPendingSubst snap)
        currentCache <- readIORef (_NameCacheRef env)
        writeIORef (_NameCacheRef env) (mergeKeepingNewEntries (_SnapNameCache snap) currentCache)

-- §3.1, §4.4.2: flip the debug-mode bit. Idempotent across two calls.
-- Works whether or not a goal is currently on the stack — the IORef
-- itself lives on the env, not on a Context.
cmdDebugToggle :: Runtime ()
cmdDebugToggle = do
    env <- askRuntimeEnv
    liftIO $ modifyIORef (_DebuggingRef env) not

-- §3.1, §4.4.2: drop the goal stack and any pending substitution so
-- the next iteration of the kernel loop sees no more work. The REPL
-- typically follows up by exiting its own loop, but the runtime
-- state is self-consistent on its own — a subsequent call to e.g.
-- `cmdShow` on a cleared state will simply see an empty stack.
cmdQuit :: Runtime ()
cmdQuit = do
    env <- askRuntimeEnv
    liftIO $ do
        writeIORef (_StackRef env) []
        writeIORef (_PendingSubst env) (VarBinding Map.empty)

-- §3.3, §4.4.2: format and return the current value of the variable
-- named `name`. Read-only — no snapshot needed. The name is taken
-- without a leading `?` (the REPL is responsible for stripping it).
-- Resolution tries the display-name cache first, then falls back to
-- the viewer's anonymous-LV convention (`V_n`/`LV_n`/`TV_n`). The
-- returned string is the formatted value (or `unbound`); the message
-- prefix is the REPL's responsibility.
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

-- §3.4 CMTT scope check: a binding `?V := t` respects the contextual
-- type iff every rigid constant and every other flexible variable
-- inside `t` is visible at `?V`'s scope level (i.e. its scope level
-- is ≤ `targetScope`). HOPU normally enforces this through
-- `isPatternRespectTo` and the up/down rules; we replicate the check
-- here so `cmdAssign` rejects out-of-scope bindings before they
-- pollute the kernel.
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

-- §3.2, §4.4.2: the binding-commit step of `:assign`. The TermNode
-- argument is already lexed/parsed/desugared/type-checked by the
-- caller (the REPL, or a library client that builds TermNodes
-- directly). cmdAssign takes a snapshot, runs the runtime-side
-- preconditions of §3.2.2 — occurs (4), pattern/scope (5),
-- consistency (6) — and either commits the binding by staging it
-- into _PendingSubst or restores the snapshot on failure. Session
-- (1), flexibility (2), and typing (3) are caller responsibilities.
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
                                -- §2.3.6 (T4): consistency under the candidate substitution.
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

-- §3.4: render a `MonoType Int` in a form the user can read at a
-- breakpoint. Free type variables (`TyVar i`) are printed as `a_i`;
-- TyMTV is shown as `?t<unique>`; `TC_Arrow` is treated as a
-- right-associative infix `->`. Precedences mirror those used by
-- `Outputable KindExpr` so the output is consistent. `TC_Unique uni`
-- is reserved for runtime-introduced ty_var references (produced by
-- `instantiateFact LO_ty_pi`'s `substTyMTV` pass) and renders as
-- `?TV_<n>` so it lines up with the CMTT context's bare-name form.
-- §1.6/§2.7 (W) write boundary: type-level fold runs immediately
-- before the structural printer touches a `MonoType Int`. The kernel
-- value itself is never rewritten — `tryFoldType` only inspects it
-- and, on match, hands back a `(name, args)` view that the printer
-- renders as `name arg1 arg2 ...`. Args are themselves passed back
-- through `showsMonoType` so nested abbreviations fold uniformly.
showsMonoType :: NotationDB -> Int -> MonoType Int -> ShowS
showsMonoType db prec t = case Notation.tryFoldType db t of
    Just (name, []) -> strstr name
    Just (name, args) ->
        let inner = strstr name . List.foldr (.) id [ strstr " " . showsMonoType db 7 a | a <- args ]
        in if prec > 6 then strstr "(" . inner . strstr ")" else inner
    Nothing -> showsMonoTypeRaw db prec t

-- Structural printer used when no abbreviation matches at this node.
-- Subterms are recursed through `showsMonoType` so a deeper match
-- (e.g. inside an `->`) still folds.
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

-- Render a `LogicVar` using the same convention as `TermNode`'s viewer
-- (`?V_n` for anonymous term-level, `?TV_n` for type-level, hint when
-- available, name when LV_Named). Diverges from the raw `Show LogicVar`
-- on `LV_Unique` (raw uses `?LV_<n>`), so the debugger output stays
-- consistent across `_substitution`, `_typing`, and the current goal.
showLVarVN :: LogicVar -> ShowS
showLVarVN (LV_ty_var uni) = strstr "?TV_" . shows (unUnique uni)
showLVarVN (LV_Unique uni (DispHint (Just s))) = strstr s
showLVarVN (LV_Unique uni (DispHint Nothing)) = strstr "?V_" . shows (unUnique uni)
showLVarVN (LV_Named name) = strstr name

-- §3.4 CMTT: render `lv : t` with `lv`'s typing context inlined as
-- `(c_i : ti, ?V_j : tj, ... |- t)`. The context is everything visible
-- to `lv` (i.e. scope ≤ scope(lv)) found in the runtime's `Labeling`:
--   • rigid constants from `_ConTypes` — atomic, no further unfolding;
--   • flexible variables from `_VarTypes` with strictly smaller
--     `Unique` than `lv` itself, recursively rendered the same way.
-- The `Unique <` guard guarantees termination (Unique IDs form a strict
-- partial order matching introduction time, so a context cannot loop
-- back into a younger variable). Empty contexts still render as
-- `(|- t)` so the CMTT shape is uniform across all LVs (including
-- `LV_Named` query variables at scope 0).
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
            -- Iterate `_VarLabel` (not `_VarTypes`) so HOPU-introduced
            -- LVs without a recorded type still appear in the context.
            -- Their type renders as `?`. `?TV_<n>` (kind-level ty-vars)
            -- appear here as bare names — they are part of the typing
            -- environment a `?V` can refer to, but they have no MonoType
            -- so no `: τ` annotation is shown for them.
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
    -- `?TV_<n>` (LV_ty_var, kind-level) appears as a bare name —
    -- no `: τ` since its sort lives one level up (Star/kind), which
    -- the MonoType-based renderer can't express. `?V_<n>` is rendered
    -- with its CMTT type, recursing through `render`.
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
    -- §3.4 typing judgments: each flexible variable in scope with its
    -- inferred type, rendered in CMTT form `?V : (Γ |- τ)` where Γ
    -- lists every visible rigid constant and flexible variable. The
    -- set comes from `_TypeInfo` (built in `Main.mkRuntimeEnv` from
    -- the type-checker's `assumptions`) for `LV_Named` query vars,
    -- and from `_VarTypes` in the runtime `Labeling` for runtime-
    -- introduced anonymous vars; both are merged here.
    , pindent (space + 4) . strstr ", " . strstr "_typing = " . plist (space + 8) (
        [ showLVarVN v . strstr " : " . showsMonoTypeIn db verbose (_CurrentLabeling ctx) v (Just typ)
        | (v, typ) <- Map.toList typeMap, v `Set.member` fvs
        ]
        ++
        -- §3.4 CMTT: iterate `_VarLabel` (not `_VarTypes`) so HOPU-
        -- introduced LVs without a recorded type still appear.
        -- `lookupLVarType` returns `Nothing` for them; the renderer
        -- shows `?` in that case. Skip `_TyVarKeys` entries — their
        -- "type" is kind-level (`*`), not a `MonoType`, so the line
        -- would carry no useful information.
        [ showLVarVN v . strstr " : " . showsMonoTypeIn db verbose (_CurrentLabeling ctx) v (lookupLVarType v (_CurrentLabeling ctx))
        | (uni, _) <- IntMap.toList (_VarLabel (_CurrentLabeling ctx))
        , not (IntMap.member uni (_TyVarKeys (_CurrentLabeling ctx)))
        , let v = LV_Unique (Unique uni) noHint
        ]
      ) . nl
    , pindent (space + 4) . strstr ", " . strstr "_thread_id = " . shows (_ContextThreadId ctx) . nl
    -- §3.1 / §3.4 BETA1: the source location of the current goal, where
    -- known. Surface-visible only when the topmost cell's goal carries
    -- an `_sloc` (§2.6.1 (c)).  Goals introduced by the runtime
    -- (cut frames, conjuncts of an `LO_and`) have no SLoc and the
    -- line shows `(none)` rather than a fabricated position.
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

instantiateFact :: Fact -> ScopeLevel -> StateT Labeling (ExceptT KernelErr (UniqueT IO)) (TermNode, TermNode)
instantiateFact fact level
    = case unfoldlNApp (rewrite HNF fact) of
        (NCon (DC (DC_LO LO_ty_pi)) _, [fact1]) -> do
            uni <- getUnique
            let var = LV_ty_var uni
                -- The `LO_ty_pi` binder's LamType slot carries the MTV
                -- key (see `Compiler.makeUniversalClosure.wrapTyVar` and
                -- `Main.eqFact`). Recovering it lets us rewrite every
                -- `TyMTV mtv` in the body to point at `uni`.
                mtvKey = case rewrite HNF fact1 of
                    NLam _ (LamType (Just (TyMTV mtv))) _ _ -> Just mtv
                    _ -> Nothing
                fact1' = case mtvKey of
                    Just mtv -> substTyMTV mtv uni fact1
                    Nothing -> fact1
            modify (enrollLabel var level)
            -- `_TyVarKeys` flags this Unique as kind-level so the
            -- debugger picks `?TV_<n>` over `?V_<n>`.
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

runLogicalOperator :: LogicalOperator -> [TermNode] -> Context -> Map.Map Constant [Fact] -> [Fact] -> ScopeLevel -> CallId -> [Cell] -> Stack -> ExceptT KernelErr (UniqueT IO) Stack
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
    = return ((ctx, mkCell facts (fact1 : hyps) level goal2 call_id : cells) : stack)
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
    | Left "ill" == evaluateA (rewrite NF rhs)
    = return stack
    | LVar x <- rewrite NF lhs
    , Right v <- evaluateA (rewrite NF rhs)
    = let theta = VarBinding (Map.singleton x (mkNCon (DC (DC_NatL v)))) in execIs (zonkLVar theta ctx) (map (zonkLVar theta) cells) stack
    | Right v <- evaluateA (rewrite NF rhs)
    , rewrite NF lhs == mkNCon (DC (DC_NatL v))
    = return ((ctx, cells) : stack)
    | otherwise
    = return ((ctx { _LeftConstraints = EvalutionConstraint (rewrite NF lhs) (rewrite NF rhs) : _LeftConstraints ctx }, cells) : stack)
runLogicalOperator logical_operator args ctx facts hyps level call_id cells stack
    = throwE (BadGoalGiven (foldlNApp (mkNCon logical_operator) args))

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
evaluateB (NApp (NApp (NApp (NCon (DC DC_eq) _) (NCon (TC (TC_Named "nat")) _) _) t1 _) t2 _) = do
    v1 <- evaluateA t1
    v2 <- evaluateA t2
    return (v1 == v2)
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

runDebugger :: TermNode -> Context -> Map.Map Constant [Fact] -> [Fact] -> ScopeLevel -> CallId -> [Cell] -> Stack -> ExceptT KernelErr (UniqueT IO) Stack
runDebugger loc_str ctx facts hyps level call_id cells stack = do
    liftIO $ writeIORef (_debuggindModeOn ctx) True
    liftIO $ putStrLn ("*** debugger called with " ++ shows loc_str "")
    return ((ctx, cells) : stack)

-- Decide a `presburger "..."` goal (§2.3.5). Walks current
-- arithmetic constraints, lifts them, renumbers everything onto a
-- shared MyVar space, and asks the solver. Succeeds by pushing the
-- continuation cells; fails by returning the bare stack.
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

-- §2.3.6: True iff the given (zonked) arithmetic constraints are
-- unsatisfiable. Two-tier evaluation: the cheap `evaluateB`
-- pre-filter is consulted first; only if it cannot decide does the
-- Presburger solver get called with `entails Φ ⊥`. Conjuncts that
-- fail to lift into the linear-integer fragment are dropped — by
-- soundness (§4.2.4) dropping can only weaken the antecedent,
-- never declare false consistency.
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

runTransition :: RuntimeEnv -> Set.Set LogicVar -> Stack -> ExceptT KernelErr (UniqueT IO) Satisfied
runTransition env free_lvars = go where
    failure :: ExceptT KernelErr (UniqueT IO) Stack
    failure = return []
    success :: (Context, [Cell]) -> ExceptT KernelErr (UniqueT IO) Stack
    success with = return [with]
    arithOpCheck :: CallId -> Context -> [Cell] -> Constant -> [Fact] -> (Integer -> Integer -> Bool) -> ExceptT KernelErr (UniqueT IO) Stack
    arithOpCheck call_id ctx cells predicate args op
        = case liftM2 op (evaluateA (args !! 0)) (evaluateA (args !! 1)) of
            Left "non" ->
                let newCtx = Context
                        { _TotalVarBinding = _TotalVarBinding ctx
                        , _CurrentLabeling = _CurrentLabeling ctx
                        , _LeftConstraints = ArithmeticConstraint (foldlNApp (mkNConLoc Nothing predicate) args) : _LeftConstraints ctx
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
    search :: Map.Map Constant [Fact] -> [Fact] -> ScopeLevel -> Constant -> [TermNode] -> Context -> [Cell] -> ExceptT KernelErr (UniqueT IO) Stack
    search facts hyps level predicate args ctx cells = do
        call_id <- getUnique
        let arithOpCheck' = arithOpCheck call_id ctx cells predicate args
        ans1 <- case predicate of
            DC DC_ge -> arithOpCheck' (>=)
            DC DC_gt -> arithOpCheck' (>)
            DC DC_le -> arithOpCheck' (<=)
            DC DC_lt -> arithOpCheck' (<)
            _ -> failure
        ans2 <- fmap concat $ forM (Map.findWithDefault [] predicate facts) $ \fact -> do
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
        ans3 <- fmap concat $ forM hyps $ \fact -> do
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
        return (ans1 ++ ans2 ++ ans3)
    dispatch :: Context -> Map.Map Constant [Fact] -> [Fact] -> ScopeLevel -> (TermNode, [TermNode]) -> CallId -> [Cell] -> Stack -> ExceptT KernelErr (UniqueT IO) Satisfied
    dispatch ctx facts hyps level (NCon predicate _, args) call_id cells stack
        | DC (DC_LO logical_operator) <- predicate
        = do
            stack' <- runLogicalOperator logical_operator args ctx facts hyps level call_id cells stack
            go stack'
        | otherwise
        = do
            stack' <- search facts hyps level predicate args ctx cells
            go (stack' ++ stack)
    dispatch ctx _facts _hyps _level (NPresburgerCheck rep freeOf _, []) _call_id cells stack
        = go (runPresburger rep freeOf ctx cells stack)
    dispatch ctx facts hyps level (t, ts) call_id cells stack = throwE (BadGoalGiven (foldlNApp t ts))
    -- §3.2.4: drain any `:assign` substitution before each step. The
    -- map is keyed by `LogicVar`, so applying `zonkLVar` to `ctx`,
    -- the active cells, and every saved frame is sufficient to
    -- propagate `?V := t` everywhere a term currently lives —
    -- including `_TotalVarBinding`, `_LeftConstraints`, every cell's
    -- `_WantedGoal` / `_GivenHypos`, and the labelling map (via the
    -- `Context` instance). The IORef is reset to `mempty` once
    -- consumed so subsequent steps see no further mutation.
    applyPending :: Stack -> ExceptT KernelErr (UniqueT IO) Stack
    applyPending [] = return []
    applyPending st@((ctx, cells) : rest) = liftIO $ do
        pending <- readIORef (_PendingSubst env)
        if Map.null (unVarBinding pending)
            then return st
            else do
                writeIORef (_PendingSubst env) (VarBinding Map.empty)
                let zonkFrame (c, cs) = (zonkLVar pending c, map (zonkLVar pending) cs)
                return (zonkFrame (ctx, cells) : map zonkFrame rest)
    go :: Stack -> ExceptT KernelErr (UniqueT IO) Satisfied
    go raw_stack = do
        stack0 <- applyPending raw_stack
        case stack0 of
            [] -> return False
            (ctx, cells) : stack -> do
                -- §4.4: publish the live stack so the debug callback (and
                -- any `cmd*` function it invokes) can observe and mutate
                -- it. We re-read it after the callback returns so that
                -- e.g. `cmdQuit` (which empties `_StackRef`) takes effect.
                liftIO $ writeIORef (_StackRef env) ((ctx, cells) : stack)
                liftIO $ do
                    dbg <- readIORef (_debuggindModeOn ctx)
                    verbose <- readIORef (_VerboseTyping env)
                    when dbg $ _PutStr env env ctx (showsCurrentState (_ModuleName env) (_NotationDB env) verbose free_lvars (_TypeInfo env) ctx cells stack "")
                stackAfterCb <- liftIO (readIORef (_StackRef env))
                -- The user's `:assign` (entered via `_PutStr`) may have
                -- arrived during the debug prompt. Re-drain so the very
                -- next dispatch sees the propagated substitution.
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
        -- overkill: | hasName v1 && not (hasName v2) = loop . Map.map (flatten (VarBinding { unVarBinding = Map.singleton v2 (LVar v1) })) . Map.delete v2
        | not (hasName v1) = loop . Map.map (flatten (VarBinding { unVarBinding = Map.singleton v1 (LVar v2) })) . Map.delete v1
        | otherwise = id
    tryMatchLVar :: TermNode -> Maybe LogicVar
    tryMatchLVar t
        = case viewNestedNLam (rewrite NF t) of
            (n, t') -> case unfoldlNApp t' of
                (LVar v, ts) -> if ts == map mkNIdx [n - 1, n - 2 .. 0] then Just v else Nothing
                _ -> Nothing
