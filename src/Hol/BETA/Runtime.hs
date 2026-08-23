{-# LANGUAGE ScopedTypeVariables #-}
module Hol.BETA.Runtime where

import Calc.Presburger.Internal
import Hol.BETA.Arith
import Hol.BETA.Debugger
import Hol.BETA.Notation (NotationDB)
import qualified Hol.BETA.Notation as Notation
import Hol.BETA.TermNode
import Hol.BETA.HOPU
import Hol.BETA.Constant
import Hol.BETA.Header
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
    | ArithmeticConstraint !ArithStore !TermNode
    | PresburgerConstraint !ArithStore !MyPresburgerFormulaRep !(Map.Map MyVar TermNode)
    deriving ()

data Cell
    = Cell
        { _GivenFacts :: Map.Map Constant [Fact]
        , _GivenHypos :: [Fact]
        , _GivenArithPremises :: ArithStore
        , _ScopeLevel :: ScopeLevel
        , _WantedGoal :: Goal
        , _CellCallId :: CallId
        }
    deriving ()

emptyArithStore :: ArithStore
emptyArithStore = ([], [])

appendArithStore :: ArithStore -> ArithStore -> ArithStore
appendArithStore (leftComparisons, leftFormulas) (rightComparisons, rightFormulas)
    = (leftComparisons ++ rightComparisons, leftFormulas ++ rightFormulas)

nullArithStore :: ArithStore -> Bool
nullArithStore (comparisons, formulas) = null comparisons && null formulas

bindArithStore :: VarBinding -> ArithStore -> ArithStore
bindArithStore theta store@(comparisons, formulas)
    = assertVarBinding theta `seq`
      assertArithStore store `seq`
      ( bindVars theta comparisons
      , [ (rep, Map.map (bindVars theta) freeOf) | (rep, freeOf) <- formulas ]
      )

arithStoreTerms :: ArithStore -> [TermNode]
arithStoreTerms (comparisons, formulas)
    = comparisons ++ concatMap (Map.elems . snd) formulas

assertArithStore :: ArithStore -> ()
assertArithStore = assertNonnegativeTerms . arithStoreTerms

assertConstraint :: Constraint -> ()
assertConstraint constraint = case constraint of
    DisagreementConstraint (lhs :=?=: rhs) ->
        assertNonnegativeIndices lhs `seq` assertNonnegativeIndices rhs
    EvalutionConstraint lhs rhs ->
        assertNonnegativeIndices lhs `seq` assertNonnegativeIndices rhs
    ArithmeticConstraint premises term ->
        assertArithStore premises `seq` assertNonnegativeIndices term
    PresburgerConstraint premises _ freeOf ->
        assertArithStore premises `seq` assertNonnegativeTerms (Map.elems freeOf)

assertConstraints :: [Constraint] -> ()
assertConstraints [] = ()
assertConstraints (constraint : rest) = assertConstraint constraint `seq` assertConstraints rest

instance Eq Constraint where
    lhs == rhs
        = assertConstraint lhs `seq`
          assertConstraint rhs `seq`
          case (lhs, rhs) of
            (DisagreementConstraint d1, DisagreementConstraint d2) -> d1 == d2
            (EvalutionConstraint l1 r1, EvalutionConstraint l2 r2) -> l1 == l2 && r1 == r2
            (ArithmeticConstraint p1 t1, ArithmeticConstraint p2 t2) -> p1 == p2 && t1 == t2
            (PresburgerConstraint p1 f1 m1, PresburgerConstraint p2 f2 m2) -> p1 == p2 && f1 == f2 && m1 == m2
            _ -> False

instance Ord Constraint where
    compare lhs rhs
        = assertConstraint lhs `seq`
          assertConstraint rhs `seq`
          case (lhs, rhs) of
            (DisagreementConstraint d1, DisagreementConstraint d2) -> compare d1 d2
            (EvalutionConstraint l1 r1, EvalutionConstraint l2 r2) -> compare l1 l2 <> compare r1 r2
            (ArithmeticConstraint p1 t1, ArithmeticConstraint p2 t2) -> compare p1 p2 <> compare t1 t2
            (PresburgerConstraint p1 f1 m1, PresburgerConstraint p2 f2 m2) -> compare p1 p2 <> compare f1 f2 <> compare m1 m2
            _ -> compare (constraintTag lhs) (constraintTag rhs)
      where
        constraintTag (DisagreementConstraint _) = 0 :: Int
        constraintTag (EvalutionConstraint _ _) = 1
        constraintTag (ArithmeticConstraint _ _) = 2
        constraintTag (PresburgerConstraint _ _ _) = 3

assertEvaluationTerms :: [(TermNode, TermNode)] -> ()
assertEvaluationTerms [] = ()
assertEvaluationTerms ((lhs, rhs) : rest)
    = assertNonnegativeIndices lhs `seq`
      assertNonnegativeIndices rhs `seq`
      assertEvaluationTerms rest

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

newtype Runtime a
    = Runtime { unRuntime :: ReaderT RuntimeEnv IO a }
    deriving ()

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
        { _SnapOwner :: IORef Stack
        , _SnapPendingOwner :: IORef LogicVarSubst
        , _SnapNameCacheOwner :: IORef NameCache
        , _SnapStack :: Stack
        , _SnapPendingSubst :: LogicVarSubst
        , _SnapNameCache :: NameCache
        }
    deriving ()

snapshot :: Runtime Snapshot
snapshot = do
    env <- askRuntimeEnv
    liftIO $ do
        st <- readIORef (_StackRef env)
        ps <- readIORef (_PendingSubst env)
        nc <- readIORef (_NameCacheRef env)
        return (Snapshot
            { _SnapOwner = _StackRef env
            , _SnapPendingOwner = _PendingSubst env
            , _SnapNameCacheOwner = _NameCacheRef env
            , _SnapStack = st
            , _SnapPendingSubst = ps
            , _SnapNameCache = nc
            })

-- A snapshot is meaningful only for the runtime whose choice stack it
-- captured.  In particular, a query/reload creates a fresh stack ref, so an
-- old debugger snapshot cannot time-travel into the new runtime.
restore :: Snapshot -> Runtime (Either ErrMsg ())
restore snap = do
    env <- askRuntimeEnv
    if _SnapOwner snap /= _StackRef env
        || _SnapPendingOwner snap /= _PendingSubst env
        || _SnapNameCacheOwner snap /= _NameCacheRef env then
        return (Left "snapshot belongs to a different runtime")
    else do
        liftIO $ do
            writeIORef (_StackRef env) (_SnapStack snap)
            writeIORef (_PendingSubst env) (_SnapPendingSubst snap)
            currentCache <- readIORef (_NameCacheRef env)
            writeIORef (_NameCacheRef env) (mergeKeepingNewEntries (_SnapNameCache snap) currentCache)
        return (Right ())

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
cmdShow name
    = do
        env <- askRuntimeEnv
        liftIO $ do
            st <- readIORef (_StackRef env)
            cache <- readIORef (_NameCacheRef env)
            pending <- readIORef (_PendingSubst env)
            let resolved = case fromDisplay name cache of
                    Just lv -> Just lv
                    Nothing -> parseAnonymousLV name `mplus` Just (LV_Named name)
            case (st, resolved) of
                (_, Nothing) -> return ("unknown variable '?" ++ name ++ "'")
                ([], _) -> return "no active goal"
                ((ctx, cells) : _, Just lv)
                    | not (assignmentTargetIsKnown env ctx cells pending lv) ->
                        return ("unknown variable '?" ++ name ++ "'")
                    | otherwise ->
                        let composed = pending <> _TotalVarBinding ctx
                            value = bindVars composed (mkLVar lv)
                        in if value == mkLVar lv
                            then return "unbound"
                            else return (prettyTerm (_NotationDB env) cache value "")

scopeEscaping :: Labeling -> ScopeLevel -> LogicVar -> TermNode -> ([Constant], [LogicVar])
scopeEscaping labeling targetScope targetLV term = assertNonnegativeIndices term `seq` walk term where
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
    walk (NPresburgerCheck _ freeOf _) = foldr (combine . walk) ([], []) (Map.elems freeOf)
    walk _ = ([], [])
    combine (a1, b1) (a2, b2) = (a1 ++ a2, b1 ++ b2)

-- Evidence that can be recovered defensively from values returned by the
-- primitive-read callback.  Unknown/custom terms intentionally carry no
-- evidence so existing embedders are not rejected; literals and proper
-- literal lists have an unambiguous ground type.  The empty list is kept
-- separate because its element type is polymorphic.
data PrimitiveTypeEvidence
    = PrimitiveExactType (MonoType Int)
    | PrimitiveEmptyList
    | PrimitiveInvalidValue
    deriving (Eq)

primitiveBindingTypeOkay :: Labeling -> LogicVar -> TermNode -> Bool
primitiveBindingTypeOkay labeling target value
    | not (Set.null (getLVars value)) = False
    | otherwise = case lookupLVarType target labeling of
        Nothing -> primitiveTypeEvidence value /= Just PrimitiveInvalidValue
        Just expected -> case primitiveTypeEvidence value of
            Nothing -> maybe False (monoTypesCouldMatch expected) (typeOfTerm labeling [] value)
            Just (PrimitiveExactType actual) -> monoTypesCouldMatch expected actual
            Just PrimitiveEmptyList -> typeCouldBeList expected
            Just PrimitiveInvalidValue -> False

monoTypesCouldMatch :: MonoType Int -> MonoType Int -> Bool
monoTypesCouldMatch (TyVar _) _ = True
monoTypesCouldMatch _ (TyVar _) = True
monoTypesCouldMatch (TyMTV _) _ = True
monoTypesCouldMatch _ (TyMTV _) = True
-- Runtime-instantiated polymorphic types are represented by fresh
-- TC_Unique constructors.  Until the surrounding query specializes them,
-- they provide no evidence of a mismatch (for example `sigma X\ read X`).
monoTypesCouldMatch (TyCon (TCon (TC_Unique _) _)) _ = True
monoTypesCouldMatch _ (TyCon (TCon (TC_Unique _) _)) = True
monoTypesCouldMatch (TyCon tc1) (TyCon tc2) = tc1 == tc2
monoTypesCouldMatch (TyApp f1 x1) (TyApp f2 x2) = monoTypesCouldMatch f1 f2 && monoTypesCouldMatch x1 x2
monoTypesCouldMatch _ _ = False

typeCouldBeList :: MonoType Int -> Bool
typeCouldBeList (TyVar _) = True
typeCouldBeList (TyMTV _) = True
typeCouldBeList (TyCon (TCon (TC_Unique _) _)) = True
typeCouldBeList (TyApp (TyCon (TCon (TC_Named "list") _)) _) = True
typeCouldBeList _ = False

primitiveTypeEvidence :: TermNode -> Maybe PrimitiveTypeEvidence
primitiveTypeEvidence value
    | not (Set.null (getLVars value)) = Just PrimitiveInvalidValue
    | otherwise = case rewrite NF value of
        NCon (DC (DC_NatL _)) _ -> Just (PrimitiveExactType mkTyNat)
        NCon (DC (DC_ChrL _)) _ -> Just (PrimitiveExactType mkTyChr)
        value' -> case primitiveListElementType value' of
            Just Nothing -> Just PrimitiveEmptyList
            Just (Just elementType) -> Just (PrimitiveExactType (mkTyList elementType))
            Nothing
                | looksLikePrimitiveList value' -> Just PrimitiveInvalidValue
                | otherwise -> Nothing

-- Nothing means "not a recognizable homogeneous primitive list"; Just
-- Nothing is the empty list; Just (Just ty) is a non-empty list of ty.
primitiveListElementType :: TermNode -> Maybe (Maybe (MonoType Int))
primitiveListElementType value
    = case primitiveListView (rewrite NF value) of
        Just Nothing -> Just Nothing
        Just (Just (item, rest)) -> do
            itemType <- primitiveExactType item
            restType <- primitiveListElementType rest
            case restType of
                Nothing -> Just (Just itemType)
                Just tailType
                    | itemType == tailType -> Just (Just itemType)
                    | otherwise -> Nothing
        Nothing -> Nothing

primitiveExactType :: TermNode -> Maybe (MonoType Int)
primitiveExactType value
    = case primitiveTypeEvidence value of
        Just (PrimitiveExactType ty) -> Just ty
        _ -> Nothing

-- Runtime values occur both with explicit type arguments (after elaboration)
-- and without them (the default REPL callback constructs the latter).
primitiveListView :: TermNode -> Maybe (Maybe (TermNode, TermNode))
primitiveListView value
    = assertNonnegativeIndices value `seq` case unfoldPrimitiveApps value of
        (NCon (DC DC_Nil) _, []) -> Just Nothing
        (NCon (DC DC_Nil) _, [_typeArg]) -> Just Nothing
        (NCon (DC DC_Cons) _, [item, rest]) -> Just (Just (item, rest))
        (NCon (DC DC_Cons) _, [_typeArg, item, rest]) -> Just (Just (item, rest))
        _ -> Nothing
    where
        unfoldPrimitiveApps = flip go []
        go (NApp fun arg _) args = go fun (arg : args)
        go term args = (term, args)

looksLikePrimitiveList :: TermNode -> Bool
looksLikePrimitiveList value = assertNonnegativeIndices value `seq` case fst (unfold value []) of
    NCon (DC DC_Nil) _ -> True
    NCon (DC DC_Cons) _ -> True
    _ -> False
    where
        unfold (NApp fun arg _) args = unfold fun (arg : args)
        unfold term args = (term, args)

-- Keep the debugger's display-name map tied to the generated variables that
-- are actually visible in the current proof state.  A source hint is used
-- when available; collisions retain the established owner and give the newer
-- variable a deterministic V_<unique> fallback.
recordVisibleLVarHints :: Stack -> NameCache -> NameCache
recordVisibleLVarHints stack0 cache0 = List.foldl' register cache0 (concatMap hintedFrame stack0) where
    register cache lv@(LV_Unique uni (DispHint (Just preferred)))
        | isJust (toDisplay lv cache) = cache
        | otherwise = recordRename lv (availableName preferred uni cache) cache
    register cache _ = cache

    availableName preferred uni cache
        | available preferred = preferred
        | otherwise = firstAvailable 0
        where
            available candidate = case fromDisplay candidate cache of
                Nothing -> True
                Just owner -> owner == LV_Unique uni noHint
            stem = "V_" ++ show (unUnique uni)
            firstAvailable n
                | available candidate = candidate
                | otherwise = firstAvailable (n + 1)
                where
                    candidate = if n == (0 :: Int) then stem else stem ++ "_" ++ show n

    hintedFrame (ctx, cells) = hintedContext ctx ++ concatMap hintedCell cells
    hintedContext ctx =
        filter isHintedUnique (Map.keys binding)
            ++ concatMap hintedTerm (Map.elems binding)
            ++ concatMap hintedConstraint (_LeftConstraints ctx)
        where
            binding = unVarBinding (_TotalVarBinding ctx)
    hintedCell cell = concatMap hintedTerm (_GivenHypos cell) ++ concatMap hintedTerm (arithStoreTerms (_GivenArithPremises cell)) ++ hintedTerm (_WantedGoal cell)

    isHintedUnique (LV_Unique _ (DispHint (Just _))) = True
    isHintedUnique _ = False

    hintedConstraint (DisagreementConstraint (lhs :=?=: rhs)) = hintedTerm lhs ++ hintedTerm rhs
    hintedConstraint (EvalutionConstraint lhs rhs) = hintedTerm lhs ++ hintedTerm rhs
    hintedConstraint (ArithmeticConstraint premises term) = concatMap hintedTerm (arithStoreTerms premises) ++ hintedTerm term
    hintedConstraint (PresburgerConstraint premises _ freeOf) = concatMap hintedTerm (arithStoreTerms premises) ++ concatMap hintedTerm (Map.elems freeOf)

    hintedTerm term = case term of
        LVar lv@(LV_Unique _ (DispHint (Just _))) -> [lv]
        LVar _ -> []
        NCon _ _ -> []
        NIdx i
            | i >= 0 -> []
            | otherwise -> undefined
        NApp t1 t2 _ -> hintedTerm t1 ++ hintedTerm t2
        NLam _ _ body _ -> hintedTerm body
        Susp body _ _ suspEnv -> hintedTerm body ++ concatMap hintedSuspItem suspEnv
        NPresburgerCheck _ freeOf _ -> concatMap hintedTerm (Map.elems freeOf)
    hintedSuspItem (Dummy _) = []
    hintedSuspItem (Binds term _) = hintedTerm term

cmdAssign :: SmallId -> TermNode -> Runtime (Either ErrMsg ())
cmdAssign name term
    = assertNonnegativeIndices term `seq` do
        env <- askRuntimeEnv
        targetLV <- liftIO $ do
            cache <- readIORef (_NameCacheRef env)
            return $ case fromDisplay name cache of
                Just lv -> lv
                Nothing -> fromMaybe (LV_Named name) (parseAnonymousLV name)
        cmdAssignTarget name targetLV term

-- | Assign a target that the caller has already resolved in the current
-- debugger state.  In particular, do not reinterpret a generated variable's
-- display hint as an unrelated 'LV_Named'.
cmdAssignVar :: LogicVar -> TermNode -> Runtime (Either ErrMsg ())
cmdAssignVar targetLV term = assertNonnegativeIndices term `seq` do
    env <- askRuntimeEnv
    cache <- liftIO (readIORef (_NameCacheRef env))
    cmdAssignTarget (fromMaybe (assignmentTargetName targetLV) (toDisplay targetLV cache)) targetLV term

assignmentTargetName :: LogicVar -> SmallId
assignmentTargetName (LV_Named name) = name
assignmentTargetName (LV_Unique uni (DispHint mhint)) = fromMaybe ("V_" ++ show (unUnique uni)) mhint
assignmentTargetName (LV_ty_var uni) = "TV_" ++ show (unUnique uni)

-- Do not let callers of the public debugger API manufacture a fresh pending
-- binding merely by naming an arbitrary LogicVar.  Generated variables are
-- registered in the current labeling; named variables normally have type
-- information, but the frame scan also covers deliberately untyped embedders.
assignmentTargetIsKnown :: RuntimeEnv -> Context -> [Cell] -> LogicVarSubst -> LogicVar -> Bool
assignmentTargetIsKnown env ctx cells pending target
    = knownByType || target `Set.member` frameVars
    where
        labeling = _CurrentLabeling ctx
        -- Generated variables carry a display hint in their identity.  An
        -- IntMap lookup alone would accept a fabricated `V_n' with the right
        -- integer but the wrong hint, producing a pending substitution that
        -- can never match the real variable.  Exact frame membership is the
        -- authority for generated variables; named query variables may also
        -- be known solely from their type environment while still unbound.
        knownByType = case target of
            LV_Named _ -> isJust (lookupLVarType target labeling) || Map.member target (_TypeInfo env)
            _ -> False
        frameVars = bindingVars (_TotalVarBinding ctx) `Set.union` bindingVars pending `Set.union` Set.unions (map constraintVars (_LeftConstraints ctx) ++ map cellVars cells)

        bindingVars (VarBinding binding) = Map.keysSet binding `Set.union` Set.unions (map getLVars (Map.elems binding))
        constraintVars (DisagreementConstraint (lhs :=?=: rhs)) = getLVars lhs `Set.union` getLVars rhs
        constraintVars (EvalutionConstraint lhs rhs) = getLVars lhs `Set.union` getLVars rhs
        constraintVars (ArithmeticConstraint premises term) = Set.unions (getLVars term : map getLVars (arithStoreTerms premises))
        constraintVars (PresburgerConstraint premises _ freeOf) = Set.unions (map getLVars (arithStoreTerms premises ++ Map.elems freeOf))
        cellVars cell = Set.unions (getLVars (_WantedGoal cell) : map getLVars (_GivenHypos cell ++ arithStoreTerms (_GivenArithPremises cell)))

cmdAssignTarget :: SmallId -> LogicVar -> TermNode -> Runtime (Either ErrMsg ())
cmdAssignTarget name targetLV term
    = assertNonnegativeIndices term `seq` do
        snap <- snapshot
        env <- askRuntimeEnv
        outcome <- liftIO $ do
            st <- readIORef (_StackRef env)
            case st of
                [] -> return (Left "no active goal")
                (ctx, activeCells) : _ -> do
                    existingPending <- readIORef (_PendingSubst env)
                    let targetKnown = assignmentTargetIsKnown env ctx activeCells existingPending targetLV
                        composed_subst = existingPending <> _TotalVarBinding ctx
                        current_target = bindVars composed_subst (mkLVar targetLV)
                        t_zonked = bindVars composed_subst term
                    if not targetKnown then
                        return (Left ("unknown or inactive variable '?" ++ name ++ "'"))
                    else if current_target /= mkLVar targetLV then
                        if assignedTermsAgree current_target t_zonked then
                            return (Right ())
                        else
                            return (Left ("variable '?" ++ name ++ "' is already bound to an incompatible value"))
                    else if targetLV `Set.member` getLVars t_zonked then
                        return (Left ("occurs check failed for '" ++ name ++ "'"))
                    else do
                        let labeling = _CurrentLabeling ctx
                            scope_target = case targetLV of
                                LV_Named _ -> 0
                                _ -> lookupLabel targetLV labeling
                            (escapedCons, escapedVars) = scopeEscaping labeling scope_target targetLV t_zonked
                        if not (null escapedCons) || not (null escapedVars) then do
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
                                constraintsAfter = zonkLVar composedAfter (_LeftConstraints ctx)
                                contextAfter = ctx
                                    { _TotalVarBinding = composedAfter
                                    , _LeftConstraints = constraintsAfter
                                    }
                                evaluationTermsAfter =
                                    [ (lhs, rhs)
                                    | EvalutionConstraint lhs rhs <- constraintsAfter
                                    ]
                                inconsistentStore =
                                    isNothing (recheckEvaluationConstraints evaluationTermsAfter)
                                        || not (storeSatisfiable contextAfter)
                            if inconsistentStore then
                                return (Left ("inconsistent with arithmetic constraints for '" ++ name ++ "'"))
                            else do
                                writeIORef (_PendingSubst env) (new_binding <> existingPending)
                                return (Right ())
        case outcome of
            Left err -> do
                restored <- restore snap
                case restored of
                    Left restoreErr -> return (Left (err ++ "; rollback failed: " ++ restoreErr))
                    Right () -> return (Left err)
            Right () -> return (Right ())

assignedTermsAgree :: TermNode -> TermNode -> Bool
assignedTermsAgree lhs rhs
    = assertNonnegativeIndices lhs `seq`
      assertNonnegativeIndices rhs `seq`
      (etaReduce (rewrite NF lhs) == etaReduce (rewrite NF rhs)
        || case arithmeticEquality lhs rhs of
            ArithEqTrue -> True
            _ -> False)

instance ZonkLVar Context where
    zonkLVar theta ctx
        = assertVarBinding theta `seq`
          assertVarBinding (_TotalVarBinding ctx) `seq`
          assertConstraints (_LeftConstraints ctx) `seq`
          Context
        { _TotalVarBinding = theta <> _TotalVarBinding ctx
        , _CurrentLabeling = zonkLVar theta (_CurrentLabeling ctx)
        , _LeftConstraints = zonkLVar theta (_LeftConstraints ctx)
        , _ContextThreadId = _ContextThreadId ctx
        , _debuggindModeOn = _debuggindModeOn ctx
        }

instance ZonkLVar Constraint where
    zonkLVar theta constraint
        = assertVarBinding theta `seq`
          assertConstraint constraint `seq`
          go constraint
      where
        go (DisagreementConstraint eqn)
            = DisagreementConstraint (bindVars theta eqn)
        go (EvalutionConstraint lhs rhs)
            | LVar x <- lhs = case Map.lookup x (unVarBinding theta) of
                Nothing -> EvalutionConstraint lhs (bindVars theta rhs)
                Just t -> ArithmeticConstraint emptyArithStore (mkNApp (mkNApp (mkNApp (mkNCon (DC DC_eq)) (mkNCon (TC (TC_Named "nat")))) t) (bindVars theta rhs))
            | otherwise = EvalutionConstraint (bindVars theta lhs) (bindVars theta rhs)
        go (ArithmeticConstraint premises arith)
            = ArithmeticConstraint (bindArithStore theta premises) (bindVars theta arith)
        go (PresburgerConstraint premises rep freeOf)
            = PresburgerConstraint (bindArithStore theta premises) rep (Map.map (bindVars theta) freeOf)

instance ZonkLVar Cell where
    zonkLVar theta (Cell facts hyps premises level goal call_id)
        = assertVarBinding theta `seq`
          assertNonnegativeTerms (concat (Map.elems facts)) `seq`
          assertNonnegativeTerms hyps `seq`
          assertArithStore premises `seq`
          assertNonnegativeIndices goal `seq`
          mkCell facts (bindVars theta hyps) (bindArithStore theta premises) level (bindVars theta goal) call_id

instance Show Constraint where
    showsPrec prec (DisagreementConstraint eqn) = showsPrec prec eqn
    showsPrec prec (EvalutionConstraint lhs rhs) = showsPrec prec lhs . strstr " is " . showsPrec prec rhs
    showsPrec prec (ArithmeticConstraint premises arith) = showsGuarded prec premises (showsPrec 0 arith)
    showsPrec prec (PresburgerConstraint premises rep freeOf) = showsGuarded prec premises (showsPrec 0 (NPresburgerCheck rep freeOf Nothing))

showsGuarded :: Int -> ArithStore -> ShowS -> ShowS
showsGuarded prec premises consequent
    | null premiseTerms = consequent
    | otherwise = parensIf (prec > 3) (strstr "(" . sepBy (strstr " & ") (map (showsPrec 0) premiseTerms) . strstr ") => " . consequent)
    where
        premiseTerms = fst premises ++ [ NPresburgerCheck rep freeOf Nothing | (rep, freeOf) <- snd premises ]
        sepBy _ [] = id
        sepBy _ [item] = item
        sepBy separator (item : items) = item . separator . sepBy separator items

mkCell :: Map.Map Constant [Fact] -> [Fact] -> ArithStore -> ScopeLevel -> Goal -> CallId -> Cell
mkCell facts hyps premises level goal call_id = goal `seq` Cell { _GivenFacts = facts, _GivenHypos = hyps, _GivenArithPremises = premises, _ScopeLevel = level, _WantedGoal = goal, _CellCallId = call_id }

showsvdash :: Show goal => Indentation -> [Fact] -> goal -> ShowS
showsvdash space [] goal = strstr "|- " . shows goal
showsvdash space [hyp] goal = shows hyp . strstr " |- " . shows goal
showsvdash space (hyp : hyps) goal = shows hyp . strstr ", " . showsvdash space hyps goal

parensIf :: Bool -> ShowS -> ShowS
parensIf True inner = strstr "(" . inner . strstr ")"
parensIf False inner = inner

showsMonoType :: NotationDB -> Int -> MonoType Int -> ShowS
showsMonoType db prec t
    = case Notation.tryFoldType db t of
        Just (name, []) -> strstr name
        Just (name, args) -> parensIf (prec > 6) inner where
            inner = strstr name . List.foldr (.) id [ strstr " " . showsMonoType db 7 a | a <- args ]
        Nothing -> showsMonoTypeRaw db prec t

showsMonoTypeRaw :: NotationDB -> Int -> MonoType Int -> ShowS
showsMonoTypeRaw _ _ (TyVar i)
    = strstr "a_" . shows i
showsMonoTypeRaw _ _ (TyMTV mtv)
    = strstr "?t" . shows mtv
showsMonoTypeRaw _ _ (TyCon (TCon (TC_Unique uni) _))
    = strstr "?TV_" . shows (unUnique uni)
showsMonoTypeRaw _ _ (TyCon (TCon tc _))
    = shows tc
showsMonoTypeRaw db prec (TyApp (TyApp (TyCon (TCon TC_Arrow _)) t1) t2)
    = parensIf (prec > 4) inner where
        inner = showsMonoType db 5 t1 . strstr " -> " . showsMonoType db 4 t2
showsMonoTypeRaw db prec (TyApp t1 t2)
    = parensIf (prec > 6) inner where
        inner = showsMonoType db 6 t1 . strstr " " . showsMonoType db 7 t2

showLVarVN :: LogicVar -> ShowS
showLVarVN (LV_ty_var uni) = strstr "?TV_" . shows (unUnique uni)
showLVarVN (LV_Unique uni (DispHint (Just s))) = strstr s
showLVarVN (LV_Unique uni (DispHint Nothing)) = strstr "?V_" . shows (unUnique uni)
showLVarVN (LV_Named name) = strstr name

showsMonoTypeIn :: NotationDB -> Bool -> Labeling -> LogicVar -> Maybe (MonoType Int) -> ShowS
showsMonoTypeIn db False _ _ mtyp
    = case mtyp of
        Just t -> showsMonoType db 0 t
        Nothing -> strstr "?"
showsMonoTypeIn db True labeling lv mtyp
    = render lv mtyp where
    render :: LogicVar -> Maybe (MonoType Int) -> ShowS
    render lv' mtyp' = prefix . strstr "|- " . renderedTy . strstr ")" where
        (scope_v, myK) = case lv' of
            LV_Named _ -> (-1, -1)
            _ -> (lookupLabel lv' labeling, lvKey lv')
        cons =
            [ renderCon uni cTyp
            | (uni, cTyp) <- IntMap.toAscList (_ConTypes labeling)
            , IntMap.findWithDefault maxBound uni (_ConLabel labeling) <= scope_v
            ]
        vars =
            [ renderVar uni
            | (uni, scp) <- IntMap.toAscList (_VarLabel labeling)
            , uni < myK
            , scp <= scope_v
            ]
        entries = cons ++ vars
        prefix = case entries of
            [] -> strstr "("
            _ -> strstr "(" . sepBy (strstr ", ") entries . strstr " "
        renderedTy = case mtyp' of
            Just t -> showsMonoType db 0 t
            Nothing -> strstr "?"
    renderCon :: Int -> MonoType Int -> ShowS
    renderCon uni cTyp = strstr "c_" . shows uni . strstr " : " . showsMonoType db 0 cTyp
    renderVar :: Int -> ShowS
    renderVar uni
        | IntMap.member uni (_TyVarKeys labeling) = strstr "?TV_" . shows uni
        | otherwise = strstr "?V_" . shows uni . strstr " : " . render innerLV mInnerTy
        where
            innerLV = LV_Unique (Unique uni) noHint
            mInnerTy = IntMap.lookup uni (_VarTypes labeling)
    sepBy :: ShowS -> [ShowS] -> ShowS
    sepBy _ [] = id
    sepBy _ [x] = x
    sepBy sep (x : xs) = x . sep . sepBy sep xs

showStackItem :: NotationDB -> Bool -> Set.Set LogicVar -> Map.Map LogicVar (MonoType Int) -> Indentation -> (Context, [Cell]) -> ShowS
showStackItem db verbose fvs typeMap space (ctx, cells)
    = strcat
        [ pindent space . strstr "+ progressings = " . plist (space + 4) [ strstr "?- [ " . showsvdash (space + 8) hyps goal . strstr " ] # call_id = " . shows call_id | Cell facts hyps premises level goal call_id <- cells ] . nl
        , pindent space . strstr "+ context = Context" . nl
        , pindent (space + 4) . strstr "{ " . strstr "_substitution = " . plist (space + 8) [ shows (LVar v) . strstr " := " . shows t | (v, t) <- Map.toList (unVarBinding (_TotalVarBinding ctx)), v `Set.member` fvs ] . nl
        , pindent (space + 4) . strstr ", " . strstr "_constraints = " . plist (space + 8) [ shows constraint | constraint <- _LeftConstraints ctx ] . nl
        , pindent (space + 4) . strstr ", " . strstr "_typing = " . plist (space + 8) typings . nl
        , pindent (space + 4) . strstr ", " . strstr "_thread_id = " . shows (_ContextThreadId ctx) . nl
        , pindent (space + 4) . strstr "}" . nl
        ]
    where
        typings = namedTypings ++ generatedTypings

        namedTypings =
            [ showLVarVN v . strstr " : " . showsMonoTypeIn db verbose (_CurrentLabeling ctx) v (Just typ)
            | (v, typ) <- Map.toList typeMap, v `Set.member` fvs
            ]

        generatedTypings =
            [ showLVarVN v . strstr " : " . showsMonoTypeIn db verbose (_CurrentLabeling ctx) v (lookupLVarType v (_CurrentLabeling ctx))
            | (uni, _) <- IntMap.toList (_VarLabel (_CurrentLabeling ctx))
            , not (IntMap.member uni (_TyVarKeys (_CurrentLabeling ctx)))
            , let v = LV_Unique (Unique uni) noHint
            ]

showsCurrentState :: NotationDB -> Bool -> Set.Set LogicVar -> Map.Map LogicVar (MonoType Int) -> Context -> [Cell] -> Stack -> ShowS
showsCurrentState db verbose fvs typeMap ctx cells stack = strcat
    [ strstr "--------------------------------" . nl
    , strstr "* The top of the current stack is:" . nl
    , showStackItem db verbose fvs typeMap 4 (ctx, cells) . nl
    , strstr "* The rest of the current stack is:" . nl
    , strcat
        [ strcat
            [ pindent 0 . strstr "- (#" . shows i . strstr ")" . nl
            , showStackItem db verbose fvs typeMap 4 item . nl
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
            instantiateFact (rewrite HNF (mkNApp fact1' (mkLVar var))) level
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
            instantiateFact (rewrite HNF (mkNApp fact1 (mkLVar var))) level
        (NCon (DC (DC_LO LO_if)) _, [conclusion, premise]) -> return (conclusion, premise)
        (NCon (DC (DC_LO logical_operator)) _, args) -> lift (throwE (BadFactGiven (foldlNApp (mkNCon logical_operator) args)))
        (t, ts) -> return (foldlNApp t ts, mkNCon LO_true)

runLogicalOperator :: UniqueM m => LogicalOperator -> [TermNode] -> Context -> Map.Map Constant [Fact] -> [Fact] -> ArithStore -> ScopeLevel -> CallId -> [Cell] -> Stack -> ExceptT KernelErr m Stack
runLogicalOperator logicalOperator args ctx facts hyps premises level callId cells stack
    = assertNonnegativeTerms args `seq`
      runLogicalOperatorUnchecked logicalOperator args ctx facts hyps premises level callId cells stack

runLogicalOperatorUnchecked :: UniqueM m => LogicalOperator -> [TermNode] -> Context -> Map.Map Constant [Fact] -> [Fact] -> ArithStore -> ScopeLevel -> CallId -> [Cell] -> Stack -> ExceptT KernelErr m Stack
runLogicalOperatorUnchecked LO_true [] ctx facts hyps premises level call_id cells stack
    = return ((ctx, cells) : stack)
runLogicalOperatorUnchecked LO_fail [] ctx facts hyps premises level call_id cells stack
    = return stack
runLogicalOperatorUnchecked LO_debug [loc_str] ctx facts hyps premises level call_id cells stack
    = runDebugger loc_str ctx facts hyps level call_id cells stack
runLogicalOperatorUnchecked LO_cut [] ctx facts hyps premises level call_id cells stack
    = return ((ctx, cells) : [ (ctx', cells') | (ctx', cells') <- stack, _ContextThreadId ctx' < call_id ])
runLogicalOperatorUnchecked LO_and [goal1, goal2] ctx facts hyps premises level call_id cells stack
    = return ((ctx, mkCell facts hyps premises level goal1 call_id : mkCell facts hyps premises level goal2 call_id : cells) : stack)
runLogicalOperatorUnchecked LO_or [goal1, goal2] ctx facts hyps premises level call_id cells stack
    = return ((ctx, mkCell facts hyps premises level goal1 call_id : cells) : (ctx, mkCell facts hyps premises level goal2 call_id : cells) : stack)
runLogicalOperatorUnchecked LO_imply [fact1, goal2] ctx facts hyps premises level call_id cells stack
    = do
        localPremises <- instantiateArithPremises fact1
        let premises' = appendArithStore premises localPremises
        return ((ctx, mkCell facts (expandAssumptions fact1 ++ hyps) premises' level goal2 call_id : cells) : stack)
runLogicalOperatorUnchecked LO_sigma [goal1] ctx facts hyps premises level call_id cells stack
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
            goal' = rewrite HNF (mkNApp goal1 (mkLVar var))
        return ((ctx { _CurrentLabeling = labeling1 }, mkCell facts hyps premises level goal' call_id : cells) : stack)
runLogicalOperatorUnchecked LO_pi [goal1] ctx facts hyps premises level call_id cells stack
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
            goal' = rewrite HNF (mkNApp goal1 (mkNCon con))
        return ((ctx { _CurrentLabeling = labeling1 }, mkCell facts hyps premises (level + 1) goal' call_id : cells) : stack)
runLogicalOperatorUnchecked LO_is [lhs, rhs] ctx facts hyps premises level call_id cells stack
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
    | not arithmeticMode
    = unifyNonArithmetic
    | otherwise
    = return ((ctx { _LeftConstraints = EvalutionConstraint lhs' rhs' : _LeftConstraints ctx }, cells) : stack)
    where
        lhs' = rewrite NF lhs
        rhs' = rewrite NF rhs
        lhsValue = evaluateA lhs'
        rhsValue = evaluateA rhs'
        arithmeticMode = isNatTerm lhs' || isNatTerm rhs' || mentionsArithmetic lhs' || mentionsArithmetic rhs'
        isNatTerm t = case rewrite NF t of
            NCon (DC (DC_NatL _)) _ -> True
            _ -> typeOfTerm (_CurrentLabeling ctx) [] t == Just mkTyNat
        bindIs x rhs_s = execIs hyps (zonkLVar theta ctx) (map (zonkLVar theta) cells) stack where
            theta = VarBinding (Map.singleton x rhs_s)
        canBindIs x t = x `Set.notMember` getLVars t && null badCons && null badVars where
                targetScope = lookupLabel x (_CurrentLabeling ctx)
                (badCons, badVars) = scopeEscaping (_CurrentLabeling ctx) targetScope x t
        unifyNonArithmetic = do
            let priorDisagreements =
                    [ eqn
                    | DisagreementConstraint eqn <- _LeftConstraints ctx
                    ]
                otherConstraints =
                    [ constraint
                    | constraint <- _LeftConstraints ctx
                    , case constraint of
                        DisagreementConstraint _ -> False
                        _ -> True
                    ]
            output <- lift (runHOPU (_CurrentLabeling ctx) ((lhs' :=?=: rhs') : priorDisagreements))
            case output of
                Nothing -> return stack
                Just (newDisagreements, HopuSol newLabeling subst) -> do
                    let ctx' = (zonkLVar subst ctx)
                            { _CurrentLabeling = newLabeling
                            , _LeftConstraints =
                                map DisagreementConstraint newDisagreements
                                    ++ zonkLVar subst otherConstraints
                            }
                    execIs hyps ctx' (zonkLVar subst cells) stack
runLogicalOperatorUnchecked logical_operator args ctx facts hyps premises level call_id cells stack
    = throwE (BadGoalGiven (foldlNApp (mkNCon logical_operator) args))

expandAssumptions :: Fact -> [Fact]
expandAssumptions fact
    = case unfoldlNApp (rewrite HNF fact) of
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

-- | Extract only the arithmetic role of a local antecedent.  Searchable local
-- clauses continue to live in '_GivenHypos'; this separate store prevents
-- comparisons and Presburger formulas from becoming predicate alternatives.
-- A @pi@ inside the antecedent is represented as an actual formula quantifier,
-- rather than as a free eigenconstant outside the implication.  Thus
-- @(pi C\ A C) => G@ means @(forall C. A C) => G@, not
-- @forall C. (A C => G)@.
instantiateArithPremises :: MonadUnique m => Fact -> m ArithStore
instantiateArithPremises = collect [] . rewrite HNF where
    collect binders fact = case unfoldlNApp (rewrite HNF fact) of
        (NCon (DC (DC_LO LO_and)) _, [fact1, fact2]) ->
            appendArithStore <$> collect binders fact1 <*> collect binders fact2
        (NCon (DC (DC_LO LO_pi)) _, [fact1]) -> do
            uni <- getUnique
            let mhint = case rewrite HNF fact1 of
                    NLam hint _ _ _ -> hint
                    _ -> Nothing
                marker = LV_Unique uni (mkHint mhint)
                fact1' = rewrite HNF (mkNApp fact1 (mkLVar marker))
            collect (binders ++ [marker]) fact1'
        (NCon (DC (DC_LO LO_ty_pi)) _, [fact1]) -> do
            uni <- getUnique
            let var = LV_ty_var uni
                mtvKey = case rewrite HNF fact1 of
                    NLam _ (LamType (Just (TyMTV mtv))) _ _ -> Just mtv
                    _ -> Nothing
                fact1' = case mtvKey of
                    Just mtv -> substTyMTV mtv uni fact1
                    Nothing -> fact1
            collect binders (rewrite HNF (mkNApp fact1' (mkLVar var)))
        (NPresburgerCheck rep freeOf _, []) ->
            let (rep', freeOf') = quantifyBinders binders rep freeOf
            in return ([], [(rep', freeOf')])
        (NCon (DC (DC_LO _)) _, _) -> return emptyArithStore
        (headTerm, args) ->
            let term = foldlNApp headTerm args
            in case liftConstraint term of
                Nothing -> return emptyArithStore
                Just lifted
                    | null binders -> return ([term], [])
                    | otherwise ->
                        let (rep', freeOf') = quantifyBinders binders (_liftedFormula lifted) (_freeOfLifted lifted)
                        in return ([], [(rep', freeOf')])

    quantifyBinders binders rep freeOf = (foldr AllF rep boundVars, freeOf') where
        (boundVars, freeOf') = List.foldl' detach ([], freeOf) binders
        detach (vars, remaining) binder =
            let (owned, unowned) = Map.partition (sameBinder binder) remaining
            in (vars ++ Map.keys owned, unowned)
        sameBinder binder term = rewrite NF term == mkLVar binder

execIs :: MonadUnique m => [Fact] -> Context -> [Cell] -> Stack -> m Stack
execIs hyps ctx cells stack
    = assertNonnegativeTerms hyps `seq`
      assertConstraints (_LeftConstraints ctx) `seq`
      case recheckEvaluationConstraints new_evaluation_constraints of
        Nothing -> return stack
        Just pendingEvaluations
            | not (storeSatisfiable (newCtx pendingEvaluations)) -> return stack
            | otherwise -> return ((newCtx pendingEvaluations, cells) : stack)
    where
        new_disagreements = [ eqn | DisagreementConstraint eqn <- _LeftConstraints ctx ]
        new_evaluation_constraints = [ (rewrite NF lhs, rewrite NF rhs) | EvalutionConstraint lhs rhs <- _LeftConstraints ctx ]
        new_arithmetic_constraints = [ (premises, rewrite NF arith) | ArithmeticConstraint premises arith <- _LeftConstraints ctx ]
        new_presburger_constraints = [ PresburgerConstraint premises rep freeOf | PresburgerConstraint premises rep freeOf <- _LeftConstraints ctx ]
        newCtx pendingEvaluations = ctx
            { _LeftConstraints =
                map DisagreementConstraint new_disagreements
                    ++ map (uncurry EvalutionConstraint) pendingEvaluations
                    ++ [ ArithmeticConstraint premises arith | (premises, arith) <- new_arithmetic_constraints, evaluateB arith /= Right True ]
                    ++ new_presburger_constraints
            }

evaluateA :: TermNode -> Either ErrMsg Integer
evaluateA term = assertNonnegativeIndices term `seq` go term where
    go (NApp (NCon (DC DC_Succ) _) t1 _)
        = do
            v1 <- go t1
            return (succ v1)
    go (NApp (NApp (NCon (DC DC_plus) _) t1 _) t2 _)
        = do
            v1 <- go t1
            v2 <- go t2
            return (v1 + v2)
    go (NApp (NApp (NCon (DC DC_minus) _) t1 _) t2 _)
        = do
            v1 <- go t1
            v2 <- go t2
            if v1 >= v2 then return (v1 - v2) else Left "ill"
    go (NApp (NApp (NCon (DC DC_mul) _) t1 _) t2 _)
        = do
            v1 <- go t1
            v2 <- go t2
            return (v1 * v2)
    go (NApp (NApp (NCon (DC DC_div) _) t1 _) t2 _)
        = do
            v1 <- go t1
            v2 <- go t2
            if v2 == 0 then Left "ill" else return (v1 `div` v2)
    go t
        = case reads (shows t "") of
            [(v, "")] -> return v
            _ -> Left "non"

-- Re-evaluate delayed `is` constraints after each substitution.  A ground
-- equality that is true is discharged, a ground mismatch or an ill-defined
-- arithmetic expression kills the branch, and genuinely non-ground pairs
-- remain in source order for the next substitution.
recheckEvaluationConstraints :: [(TermNode, TermNode)] -> Maybe [(TermNode, TermNode)]
recheckEvaluationConstraints constraints
    = assertEvaluationTerms constraints `seq`
      foldr step (Just []) constraints
  where
    step (lhs, rhs) checked
        = case (evaluateA lhs', evaluateA rhs') of
            (Right lhsValue, Right rhsValue)
                | lhsValue == rhsValue -> checked
                | otherwise -> Nothing
            (Left "ill", _) -> Nothing
            (_, Left "ill") -> Nothing
            _ -> ((lhs', rhs') :) <$> checked
        where
            lhs' = rewrite NF lhs
            rhs' = rewrite NF rhs

evaluateB :: TermNode -> Either ErrMsg Bool
evaluateB term = assertNonnegativeIndices term `seq` go term where
    go (NApp (NApp (NApp (NCon (DC DC_eq) _) (NCon (TC (TC_Named "nat")) _) _) t1 _) t2 _)
        = case arithmeticEquality t1 t2 of
            ArithEqTrue -> Right True
            ArithEqFalse -> Right False
            ArithEqUnknown -> Left "non"
    go (NApp (NApp (NCon (DC DC_le) _) t1 _) t2 _)
        = do
            v1 <- evaluateA t1
            v2 <- evaluateA t2
            return (v1 <= v2)
    go (NApp (NApp (NCon (DC DC_lt) _) t1 _) t2 _)
        = do
            v1 <- evaluateA t1
            v2 <- evaluateA t2
            return (v1 < v2)
    go (NApp (NApp (NCon (DC DC_ge) _) t1 _) t2 _)
        = do
            v1 <- evaluateA t1
            v2 <- evaluateA t2
            return (v1 >= v2)
    go (NApp (NApp (NCon (DC DC_gt) _) t1 _) t2 _)
        = do
            v1 <- evaluateA t1
            v2 <- evaluateA t2
            return (v1 > v2)
    go _
        = Left "non"

data ArithmeticEquality
    = ArithEqTrue
    | ArithEqFalse
    | ArithEqUnknown
    deriving ()

arithmeticEquality :: TermNode -> TermNode -> ArithmeticEquality
arithmeticEquality t1 t2
    = assertNonnegativeIndices t1 `seq`
      assertNonnegativeIndices t2 `seq`
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
simplifyArithmetic t
    = do
        (sawArithmetic, poly) <- Just (polyOf (rewrite NF t))
        if sawArithmetic then renderPoly (combinePoly poly) else Nothing
    where
        polyOf :: TermNode -> (Bool, [([TermNode], Integer)])
        polyOf (NCon (DC (DC_NatL n)) _) = (True, [([], n)])
        polyOf (NApp (NApp (NCon (DC DC_plus) _) t1 _) t2 _) = (saw1 || saw2 || True, p1 ++ p2) where
            (saw1, p1) = polyOf t1
            (saw2, p2) = polyOf t2
        polyOf (NApp (NApp (NCon (DC DC_mul) _) t1 _) t2 _) = (saw1 || saw2 || True, multiplyPoly p1 p2) where
            (saw1, p1) = polyOf t1
            (saw2, p2) = polyOf t2
        polyOf atom = (False, [([atom], 1)])

        multiplyPoly p1 p2 =
            [ (List.sort (factors1 ++ factors2), coeff1 * coeff2)
            | (factors1, coeff1) <- p1
            , (factors2, coeff2) <- p2
            ]

        -- Both multiplication and addition are commutative in this fragment.
        -- Keying by sorted factor lists combines like terms and Map's ascending
        -- traversal gives every polynomial a canonical monomial order,
        -- independent of the source addition tree.
        combinePoly = Map.toAscList . Map.fromListWith (+) . map canonicalTerm where
            canonicalTerm (factors, coeff) = (List.sort factors, coeff)

        renderPoly poly0
            = case filter ((/= 0) . snd) poly0 of
                [] -> Just (mkNCon (DC_NatL 0))
                terms
                    | all ((>= 0) . snd) terms -> Just (foldl1 add (map renderTerm terms))
                    | otherwise -> Nothing

        renderTerm (factors, coeff)
            = case (coeff, factors) of
                (0, _) -> mkNCon (DC_NatL 0)
                (1, []) -> mkNCon (DC_NatL 1)
                (1, factor : rest) -> foldl mul factor rest
                (_, []) -> mkNCon (DC_NatL coeff)
                (_, _) -> foldl mul (mkNCon (DC_NatL coeff)) factors

        add t1 t2 = mkNApp (mkNApp (mkNCon DC_plus) t1) t2
        mul t1 t2 = mkNApp (mkNApp (mkNCon DC_mul) t1) t2

runDebugger :: UniqueM m => TermNode -> Context -> Map.Map Constant [Fact] -> [Fact] -> ScopeLevel -> CallId -> [Cell] -> Stack -> ExceptT KernelErr m Stack
runDebugger loc_str ctx facts hyps level call_id cells stack = assertNonnegativeIndices loc_str `seq` do
    liftIO $ writeIORef (_debuggindModeOn ctx) True
    liftIO $ putStrLn ("*** debugger called with " ++ shows loc_str "")
    return ((ctx, cells) : stack)

-- | A @presburger phi@ goal retains @phi@ as a deferred constraint and succeeds
--   iff the whole store (existing constraints conjoined with @phi@) stays
--   satisfiable under the arithmetic assumptions in scope (left-hand sides of
--   enclosing @=>@). The retained constraint is carried along, re-checked as
--   bindings accumulate, and reported as a residual at query success.
runPresburger :: MyPresburgerFormulaRep -> Map.Map MyVar TermNode -> ArithStore -> Context -> [Cell] -> Stack -> Stack
runPresburger rep freeOf premises ctx cells stack
    = assertNonnegativeTerms (Map.elems freeOf) `seq`
      assertArithStore premises `seq`
      assertVarBinding (_TotalVarBinding ctx) `seq`
      dispatch
    where
        dispatch
            | not (storeSatisfiable ctx') = stack
            | presburgerEntails (arithAssumptions premises ctx) (rep, freeOfBound) = (ctx, cells) : stack
            | otherwise = (ctx', cells) : stack
        ctx' :: Context
        ctx' = ctx { _LeftConstraints = PresburgerConstraint premises rep freeOf : _LeftConstraints ctx }
        -- For the entailment test, resolve the goal's free terms under the
        -- current binding (the store-sat path zonks internally via the store).
        freeOfBound :: Map.Map MyVar TermNode
        freeOfBound = Map.map (bindVars (_TotalVarBinding ctx)) freeOf

-- | The arithmetic assumptions in scope: the comparison/presburger facts among
--   the hypotheses introduced by enclosing @=>@. Non-arithmetic hypotheses are
--   ignored (comparisons are filtered downstream by 'leafFormula').
arithAssumptions :: ArithStore -> Context -> ArithStore
arithAssumptions premises ctx = bindArithStore (_TotalVarBinding ctx) premises

-- | Validity of the lia-style implication from in-scope assumptions to the
--   retained comparison/Presburger obligations under the current binding.
storeSatisfiable :: Context -> Bool
storeSatisfiable ctx
    = assertVarBinding theta `seq`
      assertConstraints (_LeftConstraints ctx) `seq`
      presburgerGuardedStoreSat guarded
  where
    theta = _TotalVarBinding ctx
    guarded :: GuardedArithStore
    guarded = mapMaybe (guardedConstraintStore theta) (_LeftConstraints ctx)

guardedConstraintStore :: VarBinding -> Constraint -> Maybe (ArithStore, ArithStore)
guardedConstraintStore theta constraint
    = assertVarBinding theta `seq`
      assertConstraint constraint `seq`
      go constraint
  where
    go (ArithmeticConstraint premises term) =
        Just (bindArithStore theta premises, arithmeticObligation (bindVars theta term))
    go (PresburgerConstraint premises rep freeOf) =
        Just (bindArithStore theta premises, ([], [(rep, Map.map (bindVars theta) freeOf)]))
    go _ = Nothing

-- Ground false/ill comparison consequents must stay false under their captured
-- guard.  Treating an ill term as an opaque arithmetic atom would incorrectly
-- make it satisfiable; an explicitly false Presburger obligation preserves the
-- conditional semantics (and still lets an impossible premise discharge it).
arithmeticObligation :: TermNode -> ArithStore
arithmeticObligation term = assertNonnegativeIndices term `seq` case evaluateB term of
    Right True -> emptyArithStore
    Right False -> ([], [(ValF False, Map.empty)])
    Left "ill" -> ([], [(ValF False, Map.empty)])
    _ -> ([term], [])

isInconsistent :: [TermNode] -> Bool
isInconsistent arithTerms
    = assertNonnegativeTerms arithTerms `seq`
      if cheapKill then True else entails compiledHyps (ValF False)
    where
        cheapKill :: Bool
        cheapKill = List.any (\t -> evaluateB t == Right False || evaluateB t == Left "ill") arithTerms

        liftedResults :: [LiftResult]
        liftedResults = mapMaybe liftConstraint arithTerms

        allFreeTerms :: [TermNode]
        allFreeTerms = Set.toAscList $ Set.unions [ Set.fromList (map (rewrite NF) (Map.elems (_freeOfLifted lr))) | lr <- liftedResults ]

        shared :: Map.Map TermNode MyVar
        shared = Map.fromAscList (zip allFreeTerms [theMinNumOfMyVar ..])

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
    arithOpCheck :: CallId -> ArithStore -> Context -> [Cell] -> Constant -> [TermNode] -> (Integer -> Integer -> Bool) -> ExceptT KernelErr m Stack
    arithOpCheck call_id premises ctx cells predicate args@[lhs, rhs] op
        = case liftConstraint candidate of
            Nothing -> case groundResult of
                Right okay -> if okay then success (ctx, cells) else failure
                Left "ill" -> failure
                _ -> throwE (UnsupportedArithmeticConstraint candidate)
            Just lifted
                | presburgerEntails activePremises (_liftedFormula lifted, _freeOfLifted lifted)
                -> success (ctx, cells)
                | Right False <- groundResult
                , nullArithStore premises
                -> failure
                | Left "ill" <- groundResult
                -> failure
                | not (storeSatisfiable newCtx)
                -> failure
                | otherwise
                -> success (newCtx, cells)
        where
            candidate = rewrite NF (bindVars (_TotalVarBinding ctx) (foldlNApp (mkNConLoc Nothing predicate) args))
            groundResult = liftM2 op (evaluateA (bindVars (_TotalVarBinding ctx) lhs)) (evaluateA (bindVars (_TotalVarBinding ctx) rhs))
            activePremises = arithAssumptions premises ctx
            newCtx = Context
                { _TotalVarBinding = _TotalVarBinding ctx
                , _CurrentLabeling = _CurrentLabeling ctx
                , _LeftConstraints = ArithmeticConstraint premises candidate : _LeftConstraints ctx
                , _ContextThreadId = call_id
                , _debuggindModeOn = _debuggindModeOn ctx
                }
    arithOpCheck _ _ _ _ predicate args _
        = throwE (BadGoalGiven (foldlNApp (mkNCon predicate) args))
    eqOpCheck :: Context -> [Cell] -> [TermNode] -> Maybe (ExceptT KernelErr m Stack)
    eqOpCheck ctx cells [_typeArg, lhs, rhs]
        | mentionsArithmetic lhs || mentionsArithmetic rhs = case arithmeticEquality (bindVars (_TotalVarBinding ctx) lhs) (bindVars (_TotalVarBinding ctx) rhs) of
            ArithEqTrue -> Just (success (ctx, cells))
            ArithEqFalse -> Just failure
            ArithEqUnknown -> Nothing
    eqOpCheck _ _ _ = Nothing
    primitivePrint :: Context -> [TermNode] -> [Cell] -> Stack -> ExceptT KernelErr m Stack
    primitivePrint ctx args cells stack
        | Just arg <- onePrimitiveArg args
        = do
            liftIO (_PrintPrimitive env ctx (bindVars (_TotalVarBinding ctx) arg))
            return ((ctx, cells) : stack)
    primitivePrint _ args _ _ = throwE (BadGoalGiven (foldlNApp (mkNCon (DC_Named "print")) args))
    primitiveRead :: [Fact] -> Context -> [TermNode] -> [Cell] -> Stack -> ExceptT KernelErr m Stack
    primitiveRead hyps ctx args cells stack
        | Just arg <- onePrimitiveArg args
        = do
            mvalue <- liftIO (_ReadPrimitive env ctx arg)
            case mvalue of
                Nothing -> return stack
                Just value -> case rewrite NF (bindVars (_TotalVarBinding ctx) arg) of
                    LVar x
                        | canBindPrimitive x value -> bindPrimitive x value
                    arg'
                        | rewrite NF arg' == rewrite NF value -> return ((ctx, cells) : stack)
                    _ -> return stack
        where
            bindPrimitive x value = execIs hyps (zonkLVar theta ctx) (map (zonkLVar theta) cells) stack where
                theta = VarBinding (Map.singleton x value)

            canBindPrimitive x t = x `Set.notMember` getLVars t && null badCons && null badVars && primitiveBindingTypeOkay (_CurrentLabeling ctx) x t where
                targetScope = lookupLabel x (_CurrentLabeling ctx)
                (badCons, badVars) = scopeEscaping (_CurrentLabeling ctx) targetScope x t
    primitiveRead _ _ args _ _ = throwE (BadGoalGiven (foldlNApp (mkNCon (DC_Named "read")) args))
    onePrimitiveArg :: [TermNode] -> Maybe TermNode
    onePrimitiveArg [arg] = Just arg
    onePrimitiveArg [_typeArg, arg] = Just arg
    onePrimitiveArg _ = Nothing
    search :: Map.Map Constant [Fact] -> [Fact] -> ArithStore -> ScopeLevel -> Constant -> [TermNode] -> Context -> [Cell] -> ExceptT KernelErr m Stack
    search facts hyps premises level predicate args ctx cells
        = do
            call_id <- getUnique
            let arithOpCheck' = arithOpCheck call_id premises ctx cells predicate args
            case predicate of
                DC DC_eq -> do
                    -- A bare equality antecedent keeps its ordinary local
                    -- hypothesis role.  A nonempty local match block has strict
                    -- precedence; only an empty block falls through to the
                    -- arithmetic/program built-in.  In particular,
                    -- @((1 = 2) => (1 = 2))@ succeeds by assumption without a
                    -- duplicate built-in answer.
                    localAnswers <- searchHyps call_id
                    if null localAnswers then do
                        arithmeticAnswer <- sequence (eqOpCheck ctx cells args)
                        case arithmeticAnswer of
                            Just answer -> return answer
                            Nothing -> searchProgram call_id
                    else
                        return localAnswers
                DC DC_ge -> arithOpCheck' (>=)
                DC DC_gt -> arithOpCheck' (>)
                DC DC_le -> arithOpCheck' (<=)
                DC DC_lt -> arithOpCheck' (<)
                _ -> searchFacts call_id
        where
            searchFacts call_id = do
                ans2 <- searchProgram call_id
                ans3 <- searchHyps call_id
                return (ans2 ++ ans3)

            searchProgram call_id = fmap concat (forM (Map.findWithDefault [] predicate facts) (matchFact call_id))
            searchHyps call_id = fmap concat (forM hyps (matchFact call_id))

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
                                    let zonked_constraints = zonkLVar subst (_LeftConstraints ctx)
                                        new_evaluation_constraints = [ (rewrite NF lhs, rewrite NF rhs) | EvalutionConstraint lhs rhs <- zonked_constraints ]
                                        new_arithmetic_constraints = [ (premises0, rewrite NF arith) | ArithmeticConstraint premises0 arith <- zonked_constraints ]
                                        new_presburger_constraints = [ PresburgerConstraint premises0 rep freeOf | PresburgerConstraint premises0 rep freeOf <- zonked_constraints ]
                                    case recheckEvaluationConstraints new_evaluation_constraints of
                                        Nothing -> failure
                                        Just pendingEvaluations -> do
                                            let newCtx = Context
                                                    { _TotalVarBinding = zonkLVar subst (_TotalVarBinding ctx)
                                                    , _CurrentLabeling = new_labeling
                                                    , _LeftConstraints =
                                                        map DisagreementConstraint new_disagreements
                                                            ++ [ EvalutionConstraint lhs rhs | (lhs, rhs) <- pendingEvaluations ]
                                                            ++ [ ArithmeticConstraint premises0 arith | (premises0, arith) <- new_arithmetic_constraints, evaluateB (rewrite NF arith) /= Right True ]
                                                            ++ new_presburger_constraints
                                                    , _ContextThreadId = call_id
                                                    , _debuggindModeOn = _debuggindModeOn ctx
                                                    }
                                                inconsistentStore =
                                                    not (storeSatisfiable newCtx)
                                            if inconsistentStore then
                                                failure
                                            else
                                                success (newCtx, zonkLVar subst (mkCell facts new_hyps premises new_level new_goal call_id : cells))
                    _ -> failure
    dispatch :: Context -> Map.Map Constant [Fact] -> [Fact] -> ArithStore -> ScopeLevel -> (TermNode, [TermNode]) -> CallId -> [Cell] -> Stack -> ExceptT KernelErr m Satisfied
    dispatch ctx facts hyps premises level (NCon predicate _, args) call_id cells stack
        | DC (DC_LO logical_operator) <- predicate
        = do
            stack' <- runLogicalOperator logical_operator args ctx facts hyps premises level call_id cells stack
            go stack'
        | predicate == DC (DC_Named "print")
        = do
            stack' <- primitivePrint ctx args cells stack
            go stack'
        | predicate == DC (DC_Named "read")
        = do
            stack' <- primitiveRead hyps ctx args cells stack
            go stack'
        | otherwise
        = do
            stack' <- search facts hyps premises level predicate args ctx cells
            go (stack' ++ stack)
    dispatch ctx _facts _hyps premises _level (NPresburgerCheck rep freeOf _, []) _call_id cells stack
        = go (runPresburger rep freeOf premises ctx cells stack)
    dispatch ctx facts hyps premises level (t, ts) call_id cells stack
        = throwE (BadGoalGiven (foldlNApp t ts))
    applyPending :: Stack -> ExceptT KernelErr m Stack
    applyPending [] = return []
    applyPending st@((ctx, cells) : rest) = liftIO $ do
        pending <- readIORef (_PendingSubst env)
        if Map.null (unVarBinding pending) then
            return st
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
                    when dbg $ do
                        modifyIORef' (_NameCacheRef env) (recordVisibleLVarHints ((ctx, cells) : stack))
                        _PutStr env env ctx (showsCurrentState (_NotationDB env) verbose free_lvars (_TypeInfo env) ctx cells stack "")
                stackAfterCb <- liftIO (readIORef (_StackRef env))
                stack1 <- applyPending stackAfterCb
                case stack1 of
                    [] -> return False
                    (ctx', cells') : stack' -> case cells' of
                        [] -> do
                            want_more <- liftIO (_Answer env ctx')
                            if want_more then go stack' else return True
                        Cell facts hyps premises level goal call_id : rest_cells -> dispatch ctx' facts hyps premises level (unfoldlNApp (rewrite HNF goal)) call_id rest_cells stack'

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
