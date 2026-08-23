module Main where

import Control.Monad (unless)
import Control.Monad.Trans.Except (runExceptT)
import Control.Exception (SomeException, try)
import Data.IORef
import qualified Data.IntMap.Strict as IntMap
import Data.List (isInfixOf)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Hol.BETA.Debugger
import Hol.BETA.Header
import Hol.BETA.HOPU (Labeling (..), LogicVarSubst, VarBinding (..), bindVars)
import qualified Hol.BETA.Notation as Notation
import Hol.BETA.Runtime
import Hol.BETA.TermNode
import System.Exit (exitFailure)
import Z.Utils (Unique (..), execUniqueT)

assert :: String -> Bool -> IO ()
assert label okay = unless okay $ do
    putStrLn ("runtime snapshot regression failed: " ++ label)
    exitFailure

assertUndefined :: String -> IO a -> IO ()
assertUndefined label action = do
    outcome <- try (action >> return ()) :: IO (Either SomeException ())
    case outcome of
        Left _ -> return ()
        Right () -> assert label False

mkRuntimeEnv :: IORef Stack -> IORef LogicVarSubst -> IORef NameCache -> IORef [String] -> IORef Int -> IO RuntimeEnv
mkRuntimeEnv stackRef pendingRef cacheRef outputRef inputRef = do
    verboseRef <- newIORef False
    debuggingRef <- newIORef False
    return RuntimeEnv
        { _PutStr = \_ _ line -> modifyIORef' outputRef (++ [line])
        , _Answer = \_ -> return False
        , _PrintPrimitive = \_ term -> modifyIORef' outputRef (++ [show term])
        , _ReadPrimitive = \_ _ -> modifyIORef' inputRef (+ 1) >> return Nothing
        , _TypeInfo = Map.empty
        , _PendingSubst = pendingRef
        , _ProgramKindEnv = Map.fromList
            [ (TC_Arrow, KArr Star (KArr Star Star))
            , (TC_Named "list", KArr Star Star)
            , (TC_Named "o", Star)
            , (TC_Named "char", Star)
            , (TC_Named "nat", Star)
            , (TC_Named "string", Star)
            ]
        , _ProgramTypeEnv = Map.empty
        , _VerboseTyping = verboseRef
        , _StackRef = stackRef
        , _NameCacheRef = cacheRef
        , _DebuggingRef = debuggingRef
        , _NotationDB = Notation.initial
        , _ModuleName = "snapshot-regression"
        , _QueryCallId = Nothing
        }

main :: IO ()
main = do
    contextDebugRef <- newIORef False
    let cutId = Unique 10
        emptyLabeling = Labeling
            { _ConLabel = IntMap.empty
            , _VarLabel = IntMap.empty
            , _ConTypes = IntMap.empty
            , _VarTypes = IntMap.empty
            , _NamedTypes = Map.empty
            , _TyVarKeys = IntMap.empty
            , _TypeEnv = Map.empty
            }
        context = Context
            { _TotalVarBinding = mempty
            , _CurrentLabeling = emptyLabeling
            , _LeftConstraints = []
            , _ContextThreadId = cutId
            , _debuggindModeOn = contextDebugRef
            }
        cell goal = mkCell Map.empty [] ([], []) 0 (mkNCon goal) cutId
        preCutStack =
            [ (context, [cell LO_cut, cell LO_fail])
            , (context, [cell LO_true])
            ]
    stackRef <- newIORef preCutStack
    pendingRef <- newIORef mempty
    let oldVar = LV_Named "Old"
        newVar = LV_Named "New"
    cacheRef <- newIORef (recordRename oldVar "Old" initialCache)
    outputRef <- newIORef []
    inputRef <- newIORef 0
    env <- mkRuntimeEnv stackRef pendingRef cacheRef outputRef inputRef

    saved <- runRuntime snapshot env
    cutResult <- execUniqueT (runExceptT (runTransition env Set.empty preCutStack))
    assert "executed cut did not prune the same-activation alternative"
        (case cutResult of Right False -> True; _ -> False)

    _PrintPrimitive env (error "unused print context") (mkNCon (DC_NatL 7))
    _ <- _ReadPrimitive env (error "unused read context") (error "unused read term")
    modifyIORef' cacheRef (recordRename newVar "New")
    restored <- runRuntime (restore saved) env
    assert "same-runtime restore failed" (either (const False) (const True) restored)
    restoredStack <- readIORef stackRef
    assert "pre-cut alternatives were not restored" (length restoredStack == length preCutStack)
    outputAfterRestore <- readIORef outputRef
    inputAfterRestore <- readIORef inputRef
    assert "restore rewound print effects" (length outputAfterRestore == 1)
    assert "restore rewound read effects" (inputAfterRestore == 1)
    cacheAfterRestore <- readIORef cacheRef
    assert "restore discarded a post-snapshot display name" (toDisplay newVar cacheAfterRestore == Just "New")
    assert "restore lost a pre-snapshot display name" (toDisplay oldVar cacheAfterRestore == Just "Old")

    otherStackRef <- newIORef []
    otherPendingRef <- newIORef mempty
    otherCacheRef <- newIORef initialCache
    otherOutputRef <- newIORef []
    otherInputRef <- newIORef 0
    otherEnv <- mkRuntimeEnv otherStackRef otherPendingRef otherCacheRef otherOutputRef otherInputRef
    crossGeneration <- runRuntime (restore saved) otherEnv
    assert "snapshot crossed a runtime/load generation" (either (const True) (const False) crossGeneration)

    assignmentStackRef <- newIORef
        [ ( context
                { _CurrentLabeling = emptyLabeling
                    { _NamedTypes = Map.fromList
                        [ ("X", mkTyNat)
                        , ("S", mkTyList mkTyChr)
                        ] }
                }
          , [cell LO_true]
          )
        ]
    assignmentPendingRef <- newIORef mempty
    assignmentCacheRef <- newIORef initialCache
    assignmentOutputRef <- newIORef []
    assignmentInputRef <- newIORef 0
    assignmentEnv0 <- mkRuntimeEnv assignmentStackRef assignmentPendingRef assignmentCacheRef assignmentOutputRef assignmentInputRef
    let target = LV_Named "X"
        boxTypeConstructor = TC_Named "box"
        boxKind = KArr Star Star
        boxedNatType = TyApp (TyCon (TCon boxTypeConstructor boxKind)) mkTyNat
        assignmentEnv = assignmentEnv0
            { _ProgramKindEnv = Map.insert boxTypeConstructor boxKind (_ProgramKindEnv assignmentEnv0)
            , _TypeInfo = Map.fromList
                [ (target, mkTyNat)
                , (LV_Named "S", mkTyList mkTyChr)
                , (LV_Named "T", mkTyList mkTyChr)
                , (LV_Named "U", mkTyList mkTyChr)
                , (LV_Named "C", mkTyList mkTyChr)
                , (LV_Named "N", mkTyList mkTyNat)
                , (LV_Named "P", mkTyList (TyCon (TCon (TC_Unique (Unique 900)) Star)))
                , (LV_Named "B", mkTyList boxedNatType)
                ] }
    rejected <- runRuntime (cmdAssignTarget "X" target (mkNCon (DC_ChrL 'a'))) assignmentEnv
    assert "direct Runtime assignment API accepted char for nat"
        (case rejected of Left err -> "type mismatch" `isInfixOf` err; Right () -> False)
    pendingAfterReject <- readIORef assignmentPendingRef
    assert "rejected typed assignment changed pending substitution" (pendingAfterReject == mempty)
    accepted <- runRuntime (cmdAssignTarget "X" target (mkNCon (DC_NatL 3))) assignmentEnv
    assert "direct Runtime assignment API rejected a matching nat"
        (case accepted of Right () -> True; Left _ -> False)
    let stringValue = mkNApp
            (mkNApp (mkNCon DC_Cons) (mkNCon (DC_ChrL 'a')))
            (mkNCon DC_Nil)
    acceptedString <- runRuntime
        (cmdAssignTarget "S" (LV_Named "S") stringValue) assignmentEnv
    assert "direct Runtime assignment API rejected a matching list char"
        (case acceptedString of Right () -> True; Left _ -> False)
    let natTypeArg = mkNCon (TC_Named "nat")
        charTypeArg = mkNCon (TC_Named "char")
        boxedNatTypeArg = mkNApp (mkNCon boxTypeConstructor) natTypeArg
        typedNilNat = mkNApp (mkNCon DC_Nil) natTypeArg
        typedNilChar = mkNApp (mkNCon DC_Nil) charTypeArg
        typedNilBoxedNat = mkNApp (mkNCon DC_Nil) boxedNatTypeArg
        typedString = mkNApp
            (mkNApp
                (mkNApp (mkNCon DC_Cons) charTypeArg)
                (mkNCon (DC_ChrL 'a')))
            typedNilChar
        forgedTypedString = mkNApp
            (mkNApp
                (mkNApp (mkNCon DC_Cons) natTypeArg)
                (mkNCon (DC_ChrL 'a')))
            typedNilNat
        badTy = mkNApp natTypeArg natTypeArg
        badNil = mkNApp (mkNCon DC_Nil) badTy
        badCons = mkNApp
            (mkNApp
                (mkNApp (mkNCon DC_Cons) badTy)
                (mkNCon (DC_NatL 0)))
            badNil
        polymorphicListLabeling = emptyLabeling
            { _NamedTypes = Map.singleton
                "P" (mkTyList (TyCon (TCon (TC_Unique (Unique 900)) Star)))
            }
    assert "primitive list evidence accepted an ill-kinded explicit nil argument"
        (not (primitiveBindingTypeOkay polymorphicListLabeling (LV_Named "P") badNil))
    assert "primitive list evidence rejected a valid explicit nat nil"
        (primitiveBindingTypeOkay
            (emptyLabeling { _NamedTypes = Map.singleton "N" (mkTyList mkTyNat) })
            (LV_Named "N") typedNilNat)
    acceptedTypedString <- runRuntime
        (cmdAssignTarget "C" (LV_Named "C") typedString) assignmentEnv
    assert "direct Runtime assignment API rejected a valid explicit char list"
        (case acceptedTypedString of Right () -> True; Left _ -> False)
    acceptedTypedNatNil <- runRuntime
        (cmdAssignTarget "N" (LV_Named "N") typedNilNat) assignmentEnv
    assert "direct Runtime assignment API rejected a valid explicit nat nil"
        (case acceptedTypedNatNil of Right () -> True; Left _ -> False)
    acceptedCustomKindNil <- runRuntime
        (cmdAssignTarget "B" (LV_Named "B") typedNilBoxedNat) assignmentEnv
    assert "Runtime kind metadata was ignored for a valid custom type argument"
        (case acceptedCustomKindNil of Right () -> True; Left _ -> False)
    rejectedTypedCons <- runRuntime
        (cmdAssignTarget "T" (LV_Named "T") forgedTypedString) assignmentEnv
    assert "explicit list type argument was discarded at the Runtime API boundary"
        (case rejectedTypedCons of Left err -> "type mismatch" `isInfixOf` err; Right () -> False)
    rejectedTypedNil <- runRuntime
        (cmdAssignTarget "U" (LV_Named "U") typedNilNat) assignmentEnv
    assert "explicit empty-list type argument was treated as polymorphic"
        (case rejectedTypedNil of Left err -> "type mismatch" `isInfixOf` err; Right () -> False)
    rejectedIllKindedNil <- runRuntime
        (cmdAssignTarget "P" (LV_Named "P") badNil) assignmentEnv
    assert "direct Runtime assignment accepted an ill-kinded explicit nil argument"
        (case rejectedIllKindedNil of Left err -> "type mismatch" `isInfixOf` err; Right () -> False)
    rejectedIllKindedCons <- runRuntime
        (cmdAssignTarget "P" (LV_Named "P") badCons) assignmentEnv
    assert "direct Runtime assignment accepted an ill-kinded explicit cons argument"
        (case rejectedIllKindedCons of Left err -> "type mismatch" `isInfixOf` err; Right () -> False)

    malformedStackRef <- newIORef
        [ (context, [Cell Map.empty [] ([], []) 0 (NIdx (-1)) cutId]) ]
    malformedPendingRef <- newIORef mempty
    malformedCacheRef <- newIORef initialCache
    malformedOutputRef <- newIORef []
    malformedInputRef <- newIORef 0
    malformedEnv <- mkRuntimeEnv malformedStackRef malformedPendingRef malformedCacheRef malformedOutputRef malformedInputRef
    assertUndefined "snapshot accepted an out-of-domain stack"
        (runRuntime snapshot malformedEnv)

    malformedLabelStackRef <- newIORef
        [ ( context
                { _CurrentLabeling = emptyLabeling
                    { _VarLabel = IntMap.singleton 1 (-1) }
                }
          , [cell LO_true]
          )
        ]
    malformedLabelPendingRef <- newIORef mempty
    malformedLabelCacheRef <- newIORef initialCache
    malformedLabelOutputRef <- newIORef []
    malformedLabelInputRef <- newIORef 0
    malformedLabelEnv <- mkRuntimeEnv malformedLabelStackRef malformedLabelPendingRef malformedLabelCacheRef malformedLabelOutputRef malformedLabelInputRef
    assertUndefined "snapshot accepted a negative scope in the labeling"
        (runRuntime snapshot malformedLabelEnv)

    -- A custom debugger callback can replace the public stack reference.  A
    -- malformed frame hidden behind a valid terminal answer used to escape
    -- validation because that tail was never resumed.  It must be forced as
    -- soon as control returns from the callback.
    callbackDebugRef <- newIORef True
    let callbackContext = context { _debuggindModeOn = callbackDebugRef }
        callbackInitialStack = [(callbackContext, [cell LO_true])]
        callbackMalformedStack =
            [ (callbackContext, [])
            , ( callbackContext
              , [Cell Map.empty [] ([], []) 0 (NIdx (-1)) cutId]
              )
            ]
    callbackStackRef <- newIORef callbackInitialStack
    callbackPendingRef <- newIORef mempty
    callbackCacheRef <- newIORef initialCache
    callbackOutputRef <- newIORef []
    callbackInputRef <- newIORef 0
    callbackEnv0 <- mkRuntimeEnv callbackStackRef callbackPendingRef
        callbackCacheRef callbackOutputRef callbackInputRef
    let callbackEnv = callbackEnv0
            { _PutStr = \runtime _ _ ->
                writeIORef (_StackRef runtime) callbackMalformedStack
            }
    assertUndefined "debugger callback stack replacement bypassed the Runtime invariant"
        (execUniqueT (runExceptT
            (runTransition callbackEnv Set.empty callbackInitialStack)))

    let answerX = LV_Named "AnswerX"
        answerY = LV_Named "AnswerY"
        answerXTerm = mkLVar answerX
        answerYTerm = mkLVar answerY
        answerOne = mkNCon (DC_NatL 1)
        answerTwo = mkNCon (DC_NatL 2)
        answerBad = mkNApp (mkNApp (mkNCon DC_div) answerOne)
            (mkNCon (DC_NatL 0))
        answerComparison predicate lhs rhs =
            mkNApp (mkNApp (mkNCon predicate) lhs) rhs
        runAnswerContext answerContext = do
            answerStackRef <- newIORef [(answerContext, [])]
            answerPendingRef <- newIORef mempty
            answerCacheRef <- newIORef initialCache
            answerOutputRef <- newIORef []
            answerInputRef <- newIORef 0
            answerCalls <- newIORef []
            answerEnv0 <- mkRuntimeEnv answerStackRef answerPendingRef
                answerCacheRef answerOutputRef answerInputRef
            let answerEnv = answerEnv0
                    { _Answer = \ctx -> do
                        modifyIORef' answerCalls
                            (++ [ ( _LeftConstraints ctx
                                  , bindVars (_TotalVarBinding ctx) answerXTerm
                                  ) ])
                        return False
                    }
            result <- execUniqueT (runExceptT
                (runTransition answerEnv (Set.fromList [answerX, answerY])
                    [(answerContext, [])]))
            calls <- readIORef answerCalls
            return (result, calls)

    (falseAnswerResult, falseAnswerCalls) <- runAnswerContext
        (context { _LeftConstraints =
            [EvalutionConstraint answerTwo answerOne] })
    assert "answer boundary accepted a false delayed evaluation"
        (case falseAnswerResult of Right False -> null falseAnswerCalls; _ -> False)

    (partialAnswerResult, partialAnswerCalls) <- runAnswerContext
        (context { _LeftConstraints =
            [EvalutionConstraint answerBad answerYTerm] })
    assert "answer boundary accepted a partial delayed evaluation"
        (case partialAnswerResult of Right False -> null partialAnswerCalls; _ -> False)

    (delayedAnswerResult, delayedAnswerCalls) <- runAnswerContext
        (context { _LeftConstraints =
            [EvalutionConstraint answerXTerm answerOne] })
    assert "answer boundary rejected or retained a solvable delayed evaluation"
        (case (delayedAnswerResult, delayedAnswerCalls) of
            (Right True, [(constraints, value)]) ->
                null constraints && value == answerOne
            _ -> False)

    let rawGroundBinding = VarBinding (Map.singleton answerY answerOne)
    (boundDelayedResult, boundDelayedCalls) <- runAnswerContext
        (context
            { _TotalVarBinding = rawGroundBinding
            , _LeftConstraints =
                [EvalutionConstraint answerXTerm answerYTerm]
            })
    assert "raw stored binding did not solve a grounded delayed evaluation"
        (case (boundDelayedResult, boundDelayedCalls) of
            (Right True, [(constraints, value)]) ->
                null constraints && value == answerOne
            _ -> False)

    (boundTrueEvaluationResult, boundTrueEvaluationCalls) <- runAnswerContext
        (context
            { _TotalVarBinding = rawGroundBinding
            , _LeftConstraints =
                [EvalutionConstraint answerYTerm answerYTerm]
            })
    assert "raw stored binding left a true evaluation residual"
        (case (boundTrueEvaluationResult, boundTrueEvaluationCalls) of
            (Right True, [(constraints, _)]) -> null constraints
            _ -> False)

    let boundTrueComparison = answerComparison DC_ge answerYTerm answerOne
    (boundTrueArithmeticResult, boundTrueArithmeticCalls) <- runAnswerContext
        (context
            { _TotalVarBinding = rawGroundBinding
            , _LeftConstraints =
                [ArithmeticConstraint ([], []) boundTrueComparison]
            })
    assert "raw stored binding left a true arithmetic residual"
        (case (boundTrueArithmeticResult, boundTrueArithmeticCalls) of
            (Right True, [(constraints, _)]) -> null constraints
            _ -> False)

    let unknownComparison = answerComparison DC_ge answerYTerm answerOne
    (unknownAnswerResult, unknownAnswerCalls) <- runAnswerContext
        (context { _LeftConstraints =
            [ArithmeticConstraint ([], []) unknownComparison] })
    assert "answer boundary discarded a still-unknown arithmetic residual"
        (case (unknownAnswerResult, unknownAnswerCalls) of
            (Right True, [([ArithmeticConstraint premises retained], _)]) ->
                premises == ([], []) && retained == rewrite NF unknownComparison
            _ -> False)

    putStrLn "runtime snapshot/cut/I-O regressions passed"
