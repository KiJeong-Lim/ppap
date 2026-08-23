module Main where

import Control.Exception (SomeException, evaluate, try)
import Control.Monad.Trans.Except (runExceptT)
import Control.Monad.Trans.State.Strict (evalStateT)
import Data.IORef (modifyIORef', newIORef, readIORef)
import qualified Data.IntMap.Strict as IntMap
import qualified Data.List as List
import qualified Data.Map.Strict as Map
import qualified Hol.ALPHA2.Compiler as Compiler
import qualified Hol.ALPHA2.Constant as Constant
import qualified Hol.ALPHA2.Desugarer as Desugarer
import Hol.ALPHA2.Header
import Hol.ALPHA2.HOPU
import qualified Hol.ALPHA2.Main as AlphaMain
import qualified Hol.ALPHA2.PlanHolLexer as Lexer
import Hol.ALPHA2.Runtime
import Hol.ALPHA2.TermNode
import Hol.ALPHA2.TypeChecker
import qualified Hol.BETA.Header as BetaHeader
import qualified Hol.BETA.TypeChecker as BetaTC
import System.Exit (exitFailure)
import Z.Utils (Unique (..), execUniqueT)

assert :: String -> Bool -> IO ()
assert label okay
    | okay = return ()
    | otherwise = do
        putStrLn ("ALPHA2 safety regression failed: " ++ label)
        exitFailure

-- Enumerate the complete ALPHA2 search, recording one observed term from each
-- answer.  Returning True from the answer callback is important for cut tests:
-- accepting only the first answer cannot distinguish a pruned alternative from
-- an alternative which was never requested.
runAlphaAnswers
    :: [Fact]
    -> Goal
    -> TermNode
    -> IO (Either KernelErr Satisfied, [TermNode])
runAlphaAnswers facts query observed = do
    debuggingRef <- newIORef False
    answerTermsRef <- newIORef []
    let runtimeEnv = RuntimeEnv
            { _PutStr = \_ _ -> pure ()
            , _Answer = \ctx -> do
                modifyIORef' answerTermsRef
                    (rewrite NF (bindVars (_TotalVarBinding ctx) observed) :)
                pure True
            }
    result <- execUniqueT $ runExceptT $
        AlphaMain.execRuntime runtimeEnv debuggingRef
            (AlphaMain.theInitialFactDecls ++ facts) query
    answers <- reverse <$> readIORef answerTermsRef
    return (result, answers)

main :: IO ()
main = do
    let malformedKind = TyApp mkTyNat mkTyNat
    assert "malformed kind application was accepted" $ case getKindEither malformedKind of
        Left (MalformedTypeApplication _) -> True
        _ -> False
    legacyKind <- try (evaluate (getKind malformedKind))
        :: IO (Either SomeException KindExpr)
    assert "legacy pure kind API disguised an ill-kinded type as `type'" $
        case legacyKind of Left _ -> True; Right _ -> False
    malformedAlphaMGU <- runExceptT (getMGU malformedKind malformedKind)
    assert "ALPHA2 MGU accepted identical ill-kinded applications" $ case malformedAlphaMGU of
        Left (_, MalformedTypeApplication _) -> True
        _ -> False
    let malformedBetaKind = BetaHeader.TyApp BetaHeader.mkTyNat BetaHeader.mkTyNat
    malformedBetaMGU <- runExceptT (BetaTC.getMGU malformedBetaKind malformedBetaKind)
    assert "BETA MGU accepted identical ill-kinded applications" $ case malformedBetaMGU of
        Left (_, BetaTC.MalformedTypeApplication _) -> True
        _ -> False
    let betaSameNameStar = BetaHeader.TyCon
            (BetaHeader.TCon (BetaHeader.TC_Named "same_name") BetaHeader.Star)
        betaSameNameArrow = BetaHeader.TyCon
            (BetaHeader.TCon (BetaHeader.TC_Named "same_name")
                (BetaHeader.KArr BetaHeader.Star BetaHeader.Star))
    mismatchedEmbeddedKinds <- runExceptT
        (BetaTC.getMGU betaSameNameStar betaSameNameArrow)
    assert "BETA MGU ignored conflicting embedded kinds on equal constructor names" $
        case mismatchedEmbeddedKinds of
            Left (_, BetaTC.KindsAreMismatched _ _) -> True
            _ -> False
    let nestedKindLhs = BetaHeader.TyApp
            (BetaHeader.TyCon (BetaHeader.TCon (BetaHeader.TC_Named "f")
                (BetaHeader.KArr BetaHeader.Star BetaHeader.Star)))
            (BetaHeader.TyCon (BetaHeader.TCon (BetaHeader.TC_Named "a") BetaHeader.Star))
        higher = BetaHeader.KArr BetaHeader.Star BetaHeader.Star
        nestedKindRhs = BetaHeader.TyApp
            (BetaHeader.TyCon (BetaHeader.TCon (BetaHeader.TC_Named "f")
                (BetaHeader.KArr higher BetaHeader.Star)))
            (BetaHeader.TyCon (BetaHeader.TCon (BetaHeader.TC_Named "a") higher))
    nestedKindMismatch <- runExceptT (BetaTC.getMGU nestedKindLhs nestedKindRhs)
    assert "BETA MGU ignored conflicting nested kind annotations" $
        case nestedKindMismatch of
            Left (_, BetaTC.KindsAreMismatched _ _) -> True
            _ -> False
    let alphaCycleVar = Unique 110
        alphaCycle = TyMTV alphaCycleVar `mkTyArrow` mkTyNat
    alphaOccurs <- runExceptT (TyMTV alphaCycleVar ->> alphaCycle)
    assert "ALPHA2 directional matcher returned a cyclic type substitution" $
        case alphaOccurs of
            Left (_, OccursCheckFailed _ _) -> True
            _ -> False
    let betaCycleVar = Unique 111
        betaCycle = BetaHeader.TyMTV betaCycleVar
            `BetaHeader.mkTyArrow` BetaHeader.mkTyNat
    betaOccurs <- runExceptT
        ((BetaTC.->>) (BetaHeader.TyMTV betaCycleVar) betaCycle)
    assert "BETA directional matcher returned a cyclic type substitution" $
        case betaOccurs of
            Left (_, BetaTC.OccursCheckFailed _ _) -> True
            _ -> False
    let chainA = Unique 112
        chainB = Unique 113
        chainLhs = TyMTV chainA `mkTyArrow` TyMTV chainB
        chainRhs = TyMTV chainB `mkTyArrow` mkTyNat
    alphaChain <- runExceptT (chainLhs ->> chainRhs)
    assert "ALPHA2 directional substitutions were not transitively composed" $
        case alphaChain of
            Right theta -> Map.lookup chainA (getTypeSubst theta) == Just mkTyNat
            Left _ -> False

    sameRigid <- runExceptT (getMGU (TyVar 0) (TyVar 0))
    assert "equal rigid type variables failed or crashed" $ case sameRigid of
        Right _ -> True
        _ -> False
    differentRigid <- runExceptT (getMGU (TyVar 0) (TyVar 1))
    assert "different rigid type variables failed without a structured mismatch" $ case differentRigid of
        Left (_, TypesAreMismatched _ _) -> True
        _ -> False

    malformedScheme <- execUniqueT $ runExceptT $
        evalStateT (instantiateScheme (Forall [] (TyVar 0))) Map.empty
    assert "out-of-range forall index was instantiated or crashed" $ case malformedScheme of
        Left _ -> True
        _ -> False

    -- Application diagnostics must point at the expression which the user can
    -- actually fix, rather than highlighting the entire application.
    let functionLoc = SLoc (10, 2) (10, 2)
        argumentLoc = SLoc (10, 6) (10, 6)
        applicationLoc = SLoc (10, 2) (10, 6)
        nonFunctionApplication = App applicationLoc
            (Con functionLoc (DC_NatL 1))
            (Con argumentLoc (DC_NatL 2))
    nonFunctionError <- execUniqueT $ runExceptT $
        inferType Map.empty nonFunctionApplication
    assert "non-function application diagnostic did not point at function position" $
        case nonFunctionError of
            Left message -> "Cannot apply a non-function value." `List.isInfixOf` message
                && "10:2-10:2" `List.isInfixOf` message
                && not ("expected_typ" `List.isInfixOf` message)
            Right _ -> False

    let fType = mkTyNat `mkTyArrow` mkTyO
        fEnv = Map.singleton (DC_Named "f") (Forall [] fType)
        wrongArgumentApplication = App applicationLoc
            (Con functionLoc (DC_Named "f"))
            (Con argumentLoc (DC_ChrL 'x'))
    wrongArgumentError <- execUniqueT $ runExceptT $
        inferType fEnv wrongArgumentApplication
    assert "wrong-argument diagnostic did not point at argument position" $
        case wrongArgumentError of
            Left message -> "Function argument has the wrong type." `List.isInfixOf` message
                && "10:6-10:6" `List.isInfixOf` message
                && "Expected: `nat'" `List.isInfixOf` message
                && "Actual:   `char'" `List.isInfixOf` message
            Right _ -> False

    let selfVariable = Unique 120
        selfApplication = App applicationLoc
            (Var functionLoc selfVariable)
            (Var argumentLoc selfVariable)
    selfApplicationError <- execUniqueT $ runExceptT $
        inferType Map.empty selfApplication
    assert "self-application diagnostic was not reported at the whole application" $
        case selfApplicationError of
            Left message -> "Self-application requires an infinite type." `List.isInfixOf` message
                && "10:2-10:6" `List.isInfixOf` message
            Right _ -> False

    let sharedVariable = Unique 121
        earlierVariableLoc = SLoc (12, 3) (12, 3)
        conflictingVariableLoc = SLoc (12, 12) (12, 12)
        fOccurrenceLoc = SLoc (12, 1) (12, 1)
        gOccurrenceLoc = SLoc (12, 10) (12, 10)
        leftApplicationLoc = SLoc (12, 1) (12, 3)
        rightApplicationLoc = SLoc (12, 10) (12, 12)
        outerApplicationLoc = SLoc (12, 1) (12, 12)
        diagnosticEnv = Map.fromList
            [ (DC_Named "takes_nat", Forall []
                (mkTyNat `mkTyArrow` (mkTyO `mkTyArrow` mkTyO)))
            , (DC_Named "takes_char", Forall []
                (mkTyChr `mkTyArrow` mkTyO))
            ]
        sharedVariableConflict = App outerApplicationLoc
            (App leftApplicationLoc
                (Con fOccurrenceLoc (DC_Named "takes_nat"))
                (Var earlierVariableLoc sharedVariable))
            (App rightApplicationLoc
                (Con gOccurrenceLoc (DC_Named "takes_char"))
                (Var conflictingVariableLoc sharedVariable))
    sharedVariableError <- execUniqueT $ runExceptT $
        inferType diagnosticEnv sharedVariableConflict
    assert "shared-variable diagnostic lost one of the conflicting occurrences" $
        case sharedVariableError of
            Left message -> "The same logic variable has conflicting type requirements."
                    `List.isInfixOf` message
                && "Earlier occurrence at 12:3-12:3" `List.isInfixOf` message
                && "Conflicting occurrence at 12:12-12:12" `List.isInfixOf` message
                && "`nat'" `List.isInfixOf` message
                && "`char'" `List.isInfixOf` message
            Right _ -> False

    wrongResultError <- execUniqueT $ runExceptT $
        checkType Map.empty (Con argumentLoc (DC_NatL 1)) mkTyO
    assert "result-type diagnostic did not explain expected and actual types" $
        case wrongResultError of
            Left message -> "Expression has the wrong result type." `List.isInfixOf` message
                && "Expected: `o'" `List.isInfixOf` message
                && "Actual:   `nat'" `List.isInfixOf` message
                && "a query or fact must have proposition type `o'" `List.isInfixOf` message
            Right _ -> False

    unknownConstructorError <- execUniqueT $ runExceptT $
        inferType Map.empty (Con argumentLoc (DC_Named "missing"))
    assert "unknown-constructor diagnostic remained ungrammatical or location-free" $
        case unknownConstructorError of
            Left message -> "Unknown predicate or constructor `missing'." `List.isInfixOf` message
                && "10:6-10:6" `List.isInfixOf` message
                && "No type declaration" `List.isInfixOf` message
            Right _ -> False

    assert "uppercase data-constructor declaration remained unreachable after acceptance" $
        case Desugarer.makeTypeEnv Map.empty
            [(loc, (DC_Named "P", Lexer.RTyCon loc (TC_Named "o")))] Map.empty of
            Left _ -> True
            Right _ -> False
    assert "unknown type-constructor diagnostic has broken quoting" $
        case Desugarer.makeTypeEnv Map.empty
            [(loc, (DC_Named "p", Lexer.RTyCon loc (TC_Named "missing")))] Map.empty of
            Left message -> "Unknown type constructor `missing'." `List.isInfixOf` message
                && not ("coudln't" `List.isInfixOf` message)
            Right _ -> False

    let missingVarExpr = Var (loc, mkTyNat) (Unique 99)
    missingVar <- execUniqueT $ runExceptT $
        Compiler.convertWithoutChecking Map.empty [] missingVarExpr
    assert "compiler's missing free variable was not reported at its occurrence" $
        case missingVar of
            Left message -> "compiler-error[1:1-1:2]" `List.isInfixOf` message
                && "unbound internal variable #99" `List.isInfixOf` message
            Right _ -> False
    let variableHeadedFact = Var (loc, mkTyO) (Unique 100)
    assert "compiler accepted a variable-headed program fact" $
        case Compiler.validateProgramFact variableHeadedFact of
            Left _ -> True
            Right () -> False
    let betaVar = Unique 101
        pType = mkTyNat `mkTyArrow` mkTyO
        pCon = Con (loc, pType) (DC_Named "p", [])
        betaBody = App (loc, mkTyO) pCon (Var (loc, mkTyNat) betaVar)
        reducibleValidFact = App (loc, mkTyO)
            (Lam (loc, mkTyNat `mkTyArrow` mkTyO) betaVar betaBody)
            (Con (loc, mkTyNat) (DC_NatL 0, []))
    assert "compiler rejected a valid beta-reduced named clause" $
        case Compiler.validateProgramFact reducibleValidFact of
            Right () -> True
            Left _ -> False
    let bodyVar = Unique 102
        bodyGoal = Var (loc, mkTyO) bodyVar
        factIf conclusion premise = App (loc, mkTyO)
            (App (loc, mkTyO `mkTyArrow` mkTyO)
                (Con (loc, mkTyO `mkTyArrow` (mkTyO `mkTyArrow` mkTyO))
                    (DC_LO LO_if, []))
                conclusion)
            premise
        nullaryP = Con (loc, mkTyO) (DC_Named "p", [])
        nullaryQ = Con (loc, mkTyO) (DC_Named "q", [])
        nullaryR = Con (loc, mkTyO) (DC_Named "r", [])
        nullaryS = Con (loc, mkTyO) (DC_Named "s", [])
        factConjunction lhs rhs = App (loc, mkTyO)
            (App (loc, mkTyO `mkTyArrow` mkTyO)
                (Con (loc, mkTyO `mkTyArrow` (mkTyO `mkTyArrow` mkTyO))
                    (DC_LO LO_and, []))
                lhs)
            rhs
        callP = App (loc, mkTyO)
            (Con (loc, mkTyO `mkTyArrow` mkTyO) (DC_Named "call", []))
            bodyGoal
    assert "compiler installed a clause with an unanchored variable goal" $
        case Compiler.validateProgramFact (factIf nullaryP bodyGoal) of
            Left _ -> True
            Right () -> False
    assert "compiler rejected a predicate variable connected to the clause head" $
        case Compiler.validateProgramFact (factIf callP bodyGoal) of
            Right () -> True
            Left _ -> False
    let sigmaVariable = Unique 103
        sigmaVariableGoal = App (loc, mkTyO)
            (Con (loc, (mkTyO `mkTyArrow` mkTyO) `mkTyArrow` mkTyO)
                (DC_LO LO_sigma, []))
            (Lam (loc, mkTyO `mkTyArrow` mkTyO) sigmaVariable
                (Var (loc, mkTyO) sigmaVariable))
    assert "compiler treated a fresh sigma variable as a dispatchable predicate" $
        case Compiler.validateProgramFact (factIf nullaryP sigmaVariableGoal) of
            Left _ -> True
            Right () -> False
    assert "compiler accepted a clause whose global conclusion is another clause" $
        case Compiler.validateProgramFact
            (factIf (factIf nullaryP nullaryQ) nullaryR) of
            Left _ -> True
            Right () -> False
    assert "compiler accepted a nested clause hidden in a conjunctive conclusion" $
        case Compiler.validateProgramFact
            (factIf (factConjunction (factIf nullaryP nullaryQ) nullaryR) nullaryS) of
            Left _ -> True
            Right () -> False
    let forgedIndexedFact = mkNApp (mkNCon LO_pi) (mkNLam (mkNIdx 0))
    assert "fact indexing crashed or accepted a variable-headed fact" $
        case AlphaMain.addIndex [forgedIndexedFact] of
            Left (BadFactGiven _) -> True
            _ -> False

    -- ALPHA2 must implement the same predicate-activation cut barrier as BETA.
    -- These direct Runtime cases deliberately enumerate every answer.
    let named0 name = mkNCon (DC_Named name)
        named1 name arg = mkNApp (named0 name) arg
        clause conclusion premise = mkNApp (mkNApp (mkNCon LO_if) conclusion) premise
        andGoal lhs rhs = mkNApp (mkNApp (mkNCon LO_and) lhs) rhs
        orGoal lhs rhs = mkNApp (mkNApp (mkNCon LO_or) lhs) rhs
        cutThen goal = andGoal (mkNCon LO_cut) goal
        quantified body = mkNApp (mkNCon LO_pi) (mkNLam body)
        natEquality lhs rhs = mkNApp
            (mkNApp (mkNApp (mkNCon DC_eq) (mkNCon (TC_Named "nat"))) lhs)
            rhs
        cutObserved = mkLVar (LV_Named "CutObserved")
        cutFailFacts =
            [ clause (named1 "alpha_cut_fail" (mkNCon (DC_NatL 1)))
                (cutThen (mkNCon LO_fail))
            , named1 "alpha_cut_fail" (mkNCon (DC_NatL 2))
            ]
    (c1Result, c1Answers) <- runAlphaAnswers cutFailFacts
        (named1 "alpha_cut_fail" cutObserved) cutObserved
    assert "C1: cut did not prune a later clause after post-cut failure" $
        case c1Result of Right False -> null c1Answers; _ -> False

    let rightChoiceFacts =
            [ quantified (clause (named1 "alpha_right_choice" (mkNIdx 0))
                (cutThen (orGoal
                    (natEquality (mkNIdx 0) (mkNCon (DC_NatL 1)))
                    (natEquality (mkNIdx 0) (mkNCon (DC_NatL 2))))))
            ]
    (c3Result, c3Answers) <- runAlphaAnswers rightChoiceFacts
        (named1 "alpha_right_choice" cutObserved) cutObserved
    assert "C3: cut pruned alternatives first created to its right" $
        case c3Result of
            Right False -> c3Answers == map (mkNCon . DC_NatL) [1, 2]
            _ -> False

    let innerName = "alpha_cut_inner"
        outerName = "alpha_cut_outer"
        nestedCutFacts =
            [ clause (named0 innerName) (cutThen (mkNCon LO_fail))
            , named0 innerName
            , clause (named1 outerName (mkNCon (DC_NatL 1))) (named0 innerName)
            , named1 outerName (mkNCon (DC_NatL 2))
            ]
    (c4Result, c4Answers) <- runAlphaAnswers nestedCutFacts
        (named1 outerName cutObserved) cutObserved
    assert "C4: a callee-local cut pruned its caller's later clause" $
        case c4Result of
            Right False -> c4Answers == [mkNCon (DC_NatL 2)]
            _ -> False

    let topLevelCut = orGoal (cutThen (mkNCon LO_fail)) (mkNCon LO_true)
    (c5Result, c5Answers) <- runAlphaAnswers [] topLevelCut (mkNCon LO_true)
    assert "C5: a top-level cut did not commit the query activation" $
        case c5Result of Right False -> null c5Answers; _ -> False

    let x = LV_Named "X"
        xTerm = mkLVar x
        zero = mkNCon (DC_NatL 0)
        division = mkNApp (mkNApp (mkNCon DC_div) xTerm) zero
    assert "known zero denominator did not dominate an unknown numerator"
        (evaluateA division == Left "ill")

    let original = EvalutionConstraint xTerm division
        theta = VarBinding (Map.singleton x (mkNCon (DC_NatL 1)))
    assert "zonking changed delayed is into a lossy arithmetic equality" $ case zonkLVar theta original of
        EvalutionConstraint _ _ -> True
        _ -> False

    -- A non-ground natural equality must retain the definedness of both
    -- operands.  Otherwise the equality fact can disappear before HOPU later
    -- binds Y to the partial expression 1 / 0.
    let y = LV_Named "Y"
        yTerm = mkLVar y
        one = mkNCon (DC_NatL 1)
        bad = mkNApp (mkNApp (mkNCon DC_div) one) zero
        p term = mkNApp (mkNCon (DC_Named "p")) term
        natEq lhs rhs = mkNApp
            (mkNApp (mkNApp (mkNCon DC_eq) (mkNCon (TC_Named "nat"))) lhs)
            rhs
        conjunction lhs rhs = mkNApp (mkNApp (mkNCon LO_and) lhs) rhs
        implication fact goal = mkNApp (mkNApp (mkNCon LO_imply) fact) goal
        orderSensitive = implication (p bad) (conjunction (natEq yTerm yTerm) (p yTerm))
    debugRef <- newIORef False
    capturedAnswers <- newIORef []
    let runtimeEnv = RuntimeEnv
            { _PutStr = \_ _ -> pure ()
            , _Answer = \ctx -> do
                modifyIORef' capturedAnswers
                    (++ [bindVars (_TotalVarBinding ctx) yTerm])
                pure False
            }
    orderResult <- execUniqueT $ runExceptT $
        AlphaMain.execRuntime runtimeEnv debugRef AlphaMain.theInitialFactDecls orderSensitive
    answers <- readIORef capturedAnswers
    assert "natural equality erased a partial-arithmetic definedness obligation"
        (case orderResult of Right False -> null answers; _ -> False)

    let unknownVsIll = mkNApp (mkNApp (mkNCon DC_ge) yTerm) bad
    assert "unknown left comparison masked an ill-defined right operand"
        (evaluateB unknownVsIll == Left "ill")

    totalDebugRef <- newIORef False
    totalAnswerConstraints <- newIORef []
    let universallyQuantifiedP = mkNApp (mkNCon LO_pi)
            (mkNLam (p (mkNIdx 0)))
        totalQuery = implication universallyQuantifiedP
            (conjunction (natEq yTerm yTerm) (p yTerm))
        totalRuntimeEnv = RuntimeEnv
            { _PutStr = \_ _ -> pure ()
            , _Answer = \ctx -> do
                modifyIORef' totalAnswerConstraints (++ [_LeftConstraints ctx])
                pure False
            }
    totalResult <- execUniqueT $ runExceptT $
        AlphaMain.execRuntime totalRuntimeEnv totalDebugRef AlphaMain.theInitialFactDecls totalQuery
    totalConstraints <- readIORef totalAnswerConstraints
    assert "a universally defined natural variable left a spurious answer obligation"
        (case totalResult of
            Right True -> all (all (\constraint -> case constraint of
                DefinedConstraint _ -> False
                _ -> True)) totalConstraints
            _ -> False)

    -- The Runtime API itself, rather than only ALPHA2.Main's answer printer,
    -- must reject a definitely false or partial delayed `is'.  A delayed
    -- constraint that becomes true after a later HOPU binding must still
    -- reach the answer callback, with the discharged constraint removed.
    let isGoal lhs rhs = mkNApp (mkNApp (mkNCon LO_is) lhs) rhs
        runIsQuery query = do
            isDebugging <- newIORef False
            answerStates <- newIORef []
            let env = RuntimeEnv
                    { _PutStr = \_ _ -> pure ()
                    , _Answer = \ctx -> do
                        modifyIORef' answerStates
                            (++ [(_LeftConstraints ctx, bindVars (_TotalVarBinding ctx) yTerm)])
                        pure False
                    }
            result <- execUniqueT $ runExceptT $
                AlphaMain.execRuntime env isDebugging AlphaMain.theInitialFactDecls query
            states <- readIORef answerStates
            pure (result, states)

    (falseIsResult, falseIsAnswers) <- runIsQuery
        (isGoal (mkNCon (DC_NatL 2)) one)
    assert "ALPHA2 Runtime accepted the false ground evaluation `2 is 1'"
        (case falseIsResult of Right False -> null falseIsAnswers; _ -> False)

    (partialIsResult, partialIsAnswers) <- runIsQuery (isGoal bad yTerm)
    assert "ALPHA2 Runtime let a partial left operand survive delayed `is'"
        (case partialIsResult of Right False -> null partialIsAnswers; _ -> False)

    let delayedSuccess = conjunction (isGoal one yTerm) (natEq yTerm one)
    (delayedIsResult, delayedIsAnswers) <- runIsQuery delayedSuccess
    assert "ALPHA2 Runtime rejected or retained a delayed `is' that became true"
        (case (delayedIsResult, delayedIsAnswers) of
            (Right True, [(constraints, value)]) ->
                value == one
                    && all (\constraint -> case constraint of
                        EvalutionConstraint _ _ -> False
                        _ -> True) constraints
            _ -> False)

    -- Empty-cell stacks are a public Runtime entry point as well as an
    -- internal answer state.  Revalidate raw residual comparisons here so a
    -- forged snapshot cannot bypass the checks normally performed after HOPU.
    let comparison predicate lhs rhs =
            mkNApp (mkNApp (mkNCon predicate) lhs) rhs
        runRawContext binding constraints = do
            rawDebugRef <- newIORef False
            rawAnswers <- newIORef []
            let rawContext = Context
                    { _TotalVarBinding = binding
                    , _CurrentLabeling = Labeling
                        { _ConLabel = IntMap.empty
                        , _VarLabel = IntMap.empty
                        }
                    , _LeftConstraints = constraints
                    , _ContextThreadId = Unique 900
                    , _debuggindModeOn = rawDebugRef
                    }
                rawEnv = RuntimeEnv
                    { _PutStr = \_ _ -> pure ()
                    , _Answer = \ctx -> do
                        modifyIORef' rawAnswers
                            (++ [ ( _LeftConstraints ctx
                                  , bindVars (_TotalVarBinding ctx) xTerm
                                  ) ])
                        pure False
                    }
            rawResult <- execUniqueT $ runExceptT $
                runTransition rawEnv mempty [(rawContext, [])]
            answers <- readIORef rawAnswers
            pure (rawResult, answers)
        runRawArithmetic constraint =
            runRawContext mempty [ArithmeticConstraint constraint]

    let falseComparison = comparison DC_gt one (mkNCon (DC_NatL 2))
    (rawFalseResult, rawFalseAnswers) <- runRawArithmetic falseComparison
    assert "ALPHA2 raw answer boundary accepted a false arithmetic constraint"
        (case rawFalseResult of Right False -> null rawFalseAnswers; _ -> False)

    let partialComparison = comparison DC_ge yTerm bad
    (rawPartialResult, rawPartialAnswers) <- runRawArithmetic partialComparison
    assert "ALPHA2 raw answer boundary accepted a partial arithmetic constraint"
        (case rawPartialResult of Right False -> null rawPartialAnswers; _ -> False)

    let unknownComparison = comparison DC_ge yTerm one
    (rawUnknownResult, rawUnknownAnswers) <- runRawArithmetic unknownComparison
    assert "ALPHA2 raw answer boundary discarded an unresolved arithmetic constraint"
        (case (rawUnknownResult, rawUnknownAnswers) of
            (Right True, [([ArithmeticConstraint retained], _)]) ->
                retained == rewrite NF unknownComparison
            _ -> False)

    let partialBinding = VarBinding (Map.singleton y bad)
        rejectsPartial label constraints = do
            (result, rawAnswers) <- runRawContext partialBinding constraints
            assert label
                (case result of Right False -> null rawAnswers; _ -> False)
    rejectsPartial
        "ALPHA2 raw binding bypassed a partial DefinedConstraint"
        [DefinedConstraint yTerm]
    rejectsPartial
        "ALPHA2 raw binding bypassed a partial EvalutionConstraint"
        [EvalutionConstraint yTerm yTerm]
    rejectsPartial
        "ALPHA2 raw binding bypassed a partial ArithmeticConstraint"
        [ArithmeticConstraint (comparison DC_ge yTerm zero)]

    let groundBinding = VarBinding (Map.singleton y one)
    (rawGroundResult, rawGroundAnswers) <- runRawContext groundBinding
        [EvalutionConstraint xTerm yTerm]
    assert "ALPHA2 raw answer finalization did not solve a grounded delayed is"
        (case (rawGroundResult, rawGroundAnswers) of
            (Right True, [(constraints, value)]) ->
                null constraints && value == one
            _ -> False)

    assert "constant module is linked" (Constant.DC DC_plus == Constant.DC DC_plus)
    putStrLn "ALPHA2 safety regressions passed"
  where
    loc = SLoc (1, 1) (1, 2)
