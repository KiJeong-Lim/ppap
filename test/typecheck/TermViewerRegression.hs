module Main where

import Calc.Presburger.Internal (PresburgerFormula (..))
import Control.Exception (SomeException, evaluate, try)
import qualified Data.IntMap.Strict as IntMap
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import qualified Hol.ALPHA2.Header as AlphaHeader
import qualified Hol.ALPHA2.HOPU as AlphaHOPU
import qualified Hol.ALPHA2.PlanHolLexer as AlphaLexer
import qualified Hol.ALPHA2.PlanHolParser as AlphaParser
import qualified Hol.ALPHA2.Runtime as AlphaRuntime
import qualified Hol.ALPHA2.TermNode as Alpha
import qualified Hol.BETA.Arith as BetaArith
import qualified Hol.BETA.Header as BetaHeader
import qualified Hol.BETA.HOPU as BetaHOPU
import qualified Hol.BETA.Notation as BetaNotation
import qualified Hol.BETA.PlanHolLexer as BetaLexer
import qualified Hol.BETA.PlanHolParser as BetaParser
import qualified Hol.BETA.Runtime as BetaRuntime
import qualified Hol.BETA.TermNode as Beta
import Z.Utils (Unique (..), pprint)

assertEqual :: String -> String -> String -> IO ()
assertEqual label expected actual
    | expected == actual = return ()
    | otherwise = error (label ++ ": expected " ++ show expected ++ ", got " ++ show actual)

assertUndefined :: String -> IO a -> IO ()
assertUndefined label action = do
    result <- try (action >> return ()) :: IO (Either SomeException ())
    case result of
        Left _ -> return ()
        Right () -> error (label ++ ": expected undefined")

assertAlphaTermEqual :: String -> Alpha.TermNode -> Alpha.TermNode -> IO ()
assertAlphaTermEqual label expected actual
    | expected == actual = return ()
    | otherwise = error (label ++ ": ALPHA2 terms differ")

assertBetaTermEqual :: String -> Beta.TermNode -> Beta.TermNode -> IO ()
assertBetaTermEqual label expected actual
    | expected == actual = return ()
    | otherwise = error (label ++ ": BETA terms differ")

alphaNamed :: String -> Alpha.TermNode
alphaNamed = Alpha.mkLVar . Alpha.LV_Named

betaNamed :: String -> Beta.TermNode
betaNamed = Beta.mkLVar . Beta.LV_Named

main :: IO ()
main = do
    let alphaPartial = Alpha.mkNApp (Alpha.mkNCon AlphaHeader.DC_plus) (alphaNamed "W_1")
        alphaIf = Alpha.mkNApp
            (Alpha.mkNApp (Alpha.mkNCon AlphaHeader.LO_if) (alphaNamed "X"))
            (Alpha.mkNApp
                (Alpha.mkNApp (Alpha.mkNCon AlphaHeader.LO_if) (alphaNamed "Y"))
                (alphaNamed "Z"))
        betaPartial = Beta.mkNApp (Beta.mkNCon BetaHeader.DC_plus) (betaNamed "W_1")
        mixedLeft = Beta.ViewOper
            ( Beta.InfixL
                (Beta.ViewOper (Beta.InfixR (Beta.ViewLVar "A") " r " (Beta.ViewLVar "B"), 6))
                " l "
                (Beta.ViewLVar "C")
            , 6
            )
        mixedRight = Beta.ViewOper
            ( Beta.InfixR
                (Beta.ViewLVar "A")
                " r "
                (Beta.ViewOper (Beta.InfixL (Beta.ViewLVar "B") " l " (Beta.ViewLVar "C"), 6))
            , 6
            )

    assertEqual "ALPHA2 lambda avoids a free W_1" "W_2\\ W_1"
        (show (Alpha.mkNLam (alphaNamed "W_1")))
    assertEqual "ALPHA2 operator eta expansion avoids a free W_1" "W_2\\ W_1 + W_2"
        (show alphaPartial)
    assertEqual "ALPHA2 clause operator is non-associative" "X :- (Y :- Z)"
        (show alphaIf)
    assertEqual "BETA hinted lambda avoids a same-named free variable" "X1\\ X"
        (show (Beta.mkNLamHint (Just "X") (betaNamed "X")))
    assertEqual "BETA notation fold viewer resolves a bound de Bruijn index" "x\\ x"
        (pprint 0 (BetaNotation.foldTerm BetaNotation.initial
            (Beta.mkNLamHint (Just "x") (Beta.mkNIdx 0))) "")
    let foldedPresburger = pprint 0
            (BetaNotation.foldTerm BetaNotation.initial
                (Beta.NPresburgerCheck (ValF True) Map.empty Nothing)) ""
    if null foldedPresburger then
        error "BETA notation fold viewer produced an empty Presburger rendering"
    else
        return ()
    assertEqual "BETA operator eta expansion avoids a free W_1" "W_2\\ W_1 + W_2"
        (show betaPartial)
    assertEqual "mixed same-level operator on a left spine is parenthesized" "(A r B) l C"
        (pprint 0 mixedLeft "")
    assertEqual "mixed same-level operator on a right spine is parenthesized" "A r (B l C)"
        (pprint 0 mixedRight "")

    let alphaF = alphaNamed "F"
        nestedLocal = Alpha.mkNLam (Alpha.mkNIdx 0)
        etaOverNestedLocal = Alpha.mkNLam
            (Alpha.mkNApp (Alpha.mkNApp alphaF nestedLocal) (Alpha.mkNIdx 0))
        doublyNestedLocal = Alpha.mkNLam (Alpha.mkNLam (Alpha.mkNIdx 1))
        etaOverDoublyNestedLocal = Alpha.mkNLam
            (Alpha.mkNApp (Alpha.mkNApp alphaF doublyNestedLocal) (Alpha.mkNIdx 0))
        etaWithOuterReference = Alpha.mkNLam
            (Alpha.mkNApp (Alpha.mkNApp alphaF (Alpha.mkNIdx 1)) (Alpha.mkNIdx 0))
    assertAlphaTermEqual "ALPHA2 eta reduction preserves a directly nested binder"
        (Alpha.mkNApp alphaF nestedLocal)
        (AlphaHOPU.etaReduce etaOverNestedLocal)
    assertAlphaTermEqual "ALPHA2 eta reduction preserves a doubly nested binder"
        (Alpha.mkNApp alphaF doublyNestedLocal)
        (AlphaHOPU.etaReduce etaOverDoublyNestedLocal)
    assertAlphaTermEqual "ALPHA2 eta reduction shifts a reference outside the removed binder"
        (Alpha.mkNApp alphaF (Alpha.mkNIdx 0))
        (AlphaHOPU.etaReduce etaWithOuterReference)

    let betaF = betaNamed "F"
        betaNestedLocal = Beta.mkNLam (Beta.mkNIdx 0)
        betaEtaOverNestedLocal = Beta.mkNLam
            (Beta.mkNApp (Beta.mkNApp betaF betaNestedLocal) (Beta.mkNIdx 0))
        betaEtaWithOuterReference = Beta.mkNLam
            (Beta.mkNApp (Beta.mkNApp betaF (Beta.mkNIdx 1)) (Beta.mkNIdx 0))
    assertBetaTermEqual "BETA eta reduction preserves a directly nested binder"
        (Beta.mkNApp betaF betaNestedLocal)
        (BetaHOPU.etaReduce betaEtaOverNestedLocal)
    assertBetaTermEqual "BETA eta reduction shifts a reference outside the removed binder"
        (Beta.mkNApp betaF (Beta.mkNIdx 0))
        (BetaHOPU.etaReduce betaEtaWithOuterReference)

    assertUndefined "ALPHA2 negative index constructor"
        (evaluate (Alpha.mkNIdx (-1)))
    assertUndefined "BETA negative index constructor"
        (evaluate (Beta.mkNIdx (-1)))
    assertUndefined "ALPHA2 forged negative index normalization"
        (evaluate (Alpha.rewrite Alpha.NF (Alpha.NIdx (-1))))
    assertUndefined "BETA forged negative index normalization"
        (evaluate (Beta.rewrite Beta.NF (Beta.NIdx (-1))))
    assertUndefined "ALPHA2 WHNF validates an argument it would otherwise suspend"
        (evaluate (Alpha.rewrite Alpha.WHNF (Alpha.NApp (alphaNamed "F") (Alpha.NIdx (-1)))))
    assertUndefined "BETA WHNF validates an argument it would otherwise suspend"
        (evaluate (Beta.rewrite Beta.WHNF (Beta.NApp (betaNamed "F") (Beta.NIdx (-1)) Nothing)))
    assertUndefined "ALPHA2 suspension rewriting validates an unused environment"
        (evaluate (Alpha.rewriteWithSusp (alphaNamed "X") 0 0 [Alpha.Binds (Alpha.NIdx (-1)) 0] Alpha.WHNF))
    assertUndefined "BETA suspension rewriting validates an unused environment"
        (evaluate (Beta.rewriteWithSusp (betaNamed "X") 0 0 [Beta.Binds (Beta.NIdx (-1)) 0] Beta.WHNF))
    assertUndefined "ALPHA2 forged negative index viewer"
        (evaluate (length (show (Alpha.NIdx (-1)))))
    assertUndefined "BETA forged negative index viewer"
        (evaluate (length (show (Beta.NIdx (-1)))))
    assertUndefined "BETA notation-fold viewer rejects a negative index before matching"
        (evaluate (length (pprint 0 (BetaNotation.foldTerm BetaNotation.initial (Beta.NIdx (-1))) "")))
    assertUndefined "BETA notation-fold node rejects a negative index before matching"
        (evaluate (BetaNotation.foldTermAsNode BetaNotation.initial (Beta.NIdx (-1))))
    let betaEmptyLabeling = BetaHOPU.Labeling
            { BetaHOPU._ConLabel = IntMap.empty
            , BetaHOPU._VarLabel = IntMap.empty
            , BetaHOPU._ConTypes = IntMap.empty
            , BetaHOPU._VarTypes = IntMap.empty
            , BetaHOPU._NamedTypes = Map.empty
            , BetaHOPU._TyVarKeys = IntMap.empty
            , BetaHOPU._TypeEnv = Map.empty
            }
        forgedTemplateDB = BetaNotation.addNotation
            "forged_negative_template" [] (Beta.NIdx (-1)) BetaNotation.initial
    assertUndefined "ALPHA2 equality rejects a forged negative index"
        (evaluate (Alpha.NIdx (-1) == alphaNamed "X"))
    assertUndefined "ALPHA2 equality prevalidates a hidden forged negative index"
        (evaluate (alphaNamed "X" == Alpha.NApp (alphaNamed "F") (Alpha.NIdx (-1))))
    assertUndefined "ALPHA2 ordering rejects a forged negative index"
        (evaluate (compare (alphaNamed "X") (Alpha.NIdx (-1))))
    assertUndefined "BETA equality rejects a forged negative index"
        (evaluate (Beta.NIdx (-1) == betaNamed "X"))
    assertUndefined "BETA equality prevalidates a hidden forged negative index"
        (evaluate (betaNamed "X" == Beta.NApp (betaNamed "F") (Beta.NIdx (-1)) Nothing))
    assertUndefined "BETA ordering rejects a forged negative index"
        (evaluate (compare (betaNamed "X") (Beta.NIdx (-1))))
    assertUndefined "ALPHA2 free-variable collection rejects a forged negative index"
        (evaluate (Set.size (AlphaHOPU.getLVars (Alpha.NIdx (-1)))))
    assertUndefined "BETA free-variable collection rejects a forged negative index"
        (evaluate (Set.size (BetaHOPU.getLVars (Beta.NIdx (-1)))))
    assertUndefined "ALPHA2 rigidity checking rejects a forged negative index"
        (evaluate (AlphaHOPU.isRigidAtom (Alpha.NIdx (-1))))
    assertUndefined "BETA rigidity checking rejects a forged negative index"
        (evaluate (BetaHOPU.isRigidAtom (Beta.NIdx (-1))))
    assertUndefined "BETA type recovery rejects rather than recovers a forged negative index"
        (evaluate (BetaHOPU.typeOfTerm betaEmptyLabeling [] (Beta.NIdx (-1))))
    assertUndefined "BETA parameter-hint recovery rejects a forged negative index"
        (evaluate (BetaHOPU.paramHint [] (Beta.NIdx (-1))))
    assertUndefined "BETA notation registration rejects a forged template"
        (evaluate forgedTemplateDB)
    assertUndefined "BETA notation folding cannot retain a forged template"
        (evaluate (BetaNotation.foldTermAsNode forgedTemplateDB (Beta.mkNCon BetaHeader.LO_true)))
    assertUndefined "ALPHA2 suspension-item equality validates both sides"
        (evaluate (Alpha.Dummy 0 == Alpha.Binds (Alpha.NIdx (-1)) 0))
    assertUndefined "BETA suspension-item equality validates both sides"
        (evaluate (Beta.Dummy 0 == Beta.Binds (Beta.NIdx (-1)) 0))
    assertUndefined "ALPHA2 constraint comparison validates a mismatched constructor"
        (evaluate (AlphaRuntime.DisagreementConstraint (alphaNamed "X" AlphaHOPU.:=?=: alphaNamed "X")
            == AlphaRuntime.EvalutionConstraint (alphaNamed "X") (Alpha.NIdx (-1))))
    assertUndefined "BETA constraint comparison validates a mismatched constructor"
        (evaluate (BetaRuntime.DisagreementConstraint (betaNamed "X" BetaHOPU.:=?=: betaNamed "X")
            == BetaRuntime.EvalutionConstraint (betaNamed "X") (Beta.NIdx (-1))))
    assertUndefined "ALPHA2 application viewing prevalidates hidden indices"
        (evaluate (Alpha.unfoldlNApp (Alpha.NApp (alphaNamed "F") (Alpha.NIdx (-1)))))
    assertUndefined "BETA lambda viewing prevalidates the complete body"
        (evaluate (Beta.viewNestedNLam (Beta.mkNLam (Beta.NIdx (-1)))))

    let alphaInvalidBinding = AlphaHOPU.VarBinding
            (Map.singleton (Alpha.LV_Named "Bad") (Alpha.NIdx (-1)))
        betaInvalidBinding = BetaHOPU.VarBinding
            (Map.singleton (Beta.LV_Named "Bad") (Beta.NIdx (-1)))
    assertUndefined "ALPHA2 empty substitution still validates its input collection"
        (evaluate (length (AlphaHOPU.bindVars mempty [Alpha.NIdx (-1)])))
    assertUndefined "BETA empty substitution still validates its input collection"
        (evaluate (length (BetaHOPU.bindVars mempty [Beta.NIdx (-1)])))
    assertUndefined "ALPHA2 substitution validates an otherwise unused binding"
        (evaluate (AlphaHOPU.flatten alphaInvalidBinding (alphaNamed "X")))
    assertUndefined "BETA substitution validates an otherwise unused binding"
        (evaluate (BetaHOPU.flatten betaInvalidBinding (betaNamed "X")))
    assertUndefined "ALPHA2 substitution comparison validates all mapped terms"
        (evaluate (alphaInvalidBinding == mempty))
    assertUndefined "BETA substitution comparison validates all mapped terms"
        (evaluate (betaInvalidBinding == mempty))

    let alphaNonThenNegative = Alpha.mkNApp
            (Alpha.mkNApp (Alpha.mkNCon AlphaHeader.DC_plus) (alphaNamed "non_numeric"))
            (Alpha.NIdx (-1))
        betaNonThenNegative = Beta.mkNApp
            (Beta.mkNApp (Beta.mkNCon BetaHeader.DC_plus) (betaNamed "non_numeric"))
            (Beta.NIdx (-1))
        alphaFalseComparison = Alpha.mkNApp
            (Alpha.mkNApp (Alpha.mkNCon AlphaHeader.DC_lt) (Alpha.mkNCon (AlphaHeader.DC_NatL 0)))
            (Alpha.mkNCon (AlphaHeader.DC_NatL 0))
        betaFalseComparison = Beta.mkNApp
            (Beta.mkNApp (Beta.mkNCon BetaHeader.DC_lt) (Beta.mkNCon (BetaHeader.DC_NatL 0)))
            (Beta.mkNCon (BetaHeader.DC_NatL 0))
        betaIllArithmetic = Beta.mkNApp
            (Beta.mkNApp (Beta.mkNCon BetaHeader.DC_minus) (Beta.mkNCon (BetaHeader.DC_NatL 0)))
            (Beta.mkNCon (BetaHeader.DC_NatL 1))
    assertUndefined "ALPHA2 arithmetic evaluation prevalidates a skipped operand"
        (evaluate (AlphaRuntime.evaluateA alphaNonThenNegative))
    assertUndefined "BETA arithmetic evaluation prevalidates a skipped operand"
        (evaluate (BetaRuntime.evaluateA betaNonThenNegative))
    assertUndefined "ALPHA2 boolean evaluation rejects its catch-all negative input"
        (evaluate (AlphaRuntime.evaluateB (Alpha.NIdx (-1))))
    assertUndefined "BETA boolean evaluation rejects its catch-all negative input"
        (evaluate (BetaRuntime.evaluateB (Beta.NIdx (-1))))
    assertUndefined "ALPHA2 arithmetic list checking prevalidates after an early false"
        (evaluate (AlphaRuntime.arithmeticConstraintsBad [alphaFalseComparison, Alpha.NIdx (-1)]))
    assertUndefined "BETA arithmetic equality prevalidates after an early ill operand"
        (evaluate (BetaRuntime.arithmeticEquality betaIllArithmetic (Beta.NIdx (-1))))
    assertUndefined "BETA evaluation-constraint checking prevalidates after an early mismatch"
        (evaluate (BetaRuntime.recheckEvaluationConstraints
            [ (Beta.mkNCon (BetaHeader.DC_NatL 0), Beta.mkNCon (BetaHeader.DC_NatL 1))
            , (Beta.NIdx (-1), Beta.mkNCon (BetaHeader.DC_NatL 0))
            ]))
    assertUndefined "BETA inconsistency checking prevalidates after an early false"
        (evaluate (BetaRuntime.isInconsistent [betaFalseComparison, Beta.NIdx (-1)]))
    assertUndefined "BETA arithmetic obligation rejects a forged negative input"
        (evaluate (BetaRuntime.arithmeticObligation (Beta.NIdx (-1))))
    assertUndefined "BETA scope checking rejects a forged negative input"
        (evaluate (BetaRuntime.scopeEscaping betaEmptyLabeling 0 (Beta.LV_Named "X") (Beta.NIdx (-1))))
    assertUndefined "BETA primitive-list matching rejects a forged negative input"
        (evaluate (BetaRuntime.primitiveListView (Beta.NIdx (-1))))
    assertUndefined "BETA debugger assignment rejects a forged term before inspecting state"
        (evaluate (BetaRuntime.cmdAssignTarget "X" (Beta.LV_Named "X") (Beta.NIdx (-1))))
    assertUndefined "BETA type substitution rejects a forged negative input"
        (evaluate (Beta.substTyMTV (Unique 1) (Unique 2) (Beta.NIdx (-1))))

    let negativeLoc = BetaHeader.SLoc (1, 1) (1, 1)
        invalidNamedEnv = Map.singleton "Unused" (Beta.NIdx (-1))
        invalidFreeMap = Map.singleton 1 (Beta.NIdx (-1))
        invalidArithStore :: BetaArith.ArithStore
        invalidArithStore = ([], [(ValF True, invalidFreeMap)])
        emptyArithStore :: BetaArith.ArithStore
        emptyArithStore = ([], [])
    assertUndefined "Presburger parsing validates an unused environment binding"
        (evaluate (BetaArith.parsePresburger negativeLoc "0 = 0" invalidNamedEnv))
    assertUndefined "Presburger installation validates an unused environment binding"
        (evaluate (BetaArith.installPresburgerWithEnv invalidNamedEnv (Beta.mkNCon BetaHeader.LO_true)))
    assertUndefined "Presburger zonking validates an unused free-term binding"
        (evaluate (BetaArith.zonkPresburger invalidFreeMap (ValF True)))
    assertUndefined "Presburger renumbering validates an unused shared key"
        (evaluate (BetaArith.renumberFormula (Map.singleton (Beta.NIdx (-1)) 1) Map.empty (ValF True)))
    assertUndefined "Arithmetic entailment validates hypotheses before rejecting the goal"
        (evaluate (BetaArith.arithEntails [Beta.NIdx (-1)] (Beta.mkNCon BetaHeader.LO_true)))
    assertUndefined "Presburger validity validates an unused free-term binding"
        (evaluate (BetaArith.presburgerValid (ValF True) invalidFreeMap))
    assertUndefined "Presburger entailment validates an unused free-term binding"
        (evaluate (BetaArith.presburgerEntails emptyArithStore (ValF True, invalidFreeMap)))
    assertUndefined "Presburger store checking validates an unused formula environment"
        (evaluate (BetaArith.presburgerStoreSat invalidArithStore emptyArithStore))
    assertUndefined "Guarded Presburger checking validates an unused formula environment"
        (evaluate (BetaArith.presburgerGuardedStoreSat [(invalidArithStore, emptyArithStore)]))
    assertUndefined "ALPHA2 negative lambda nesting depth"
        (evaluate (Alpha.makeNestedNLam (-1) (alphaNamed "X")))
    assertUndefined "BETA negative lambda nesting depth"
        (evaluate (Beta.makeNestedNLam (-1) (betaNamed "X")))

    let alphaLoc = AlphaHeader.SLoc (1, 1) (1, 1)
        betaLoc = BetaHeader.SLoc (1, 1) (1, 1)
    case AlphaParser.runHolParser [AlphaLexer.T_lex_error alphaLoc] of
        Left (Just (AlphaLexer.T_lex_error _)) -> return ()
        _ -> error "ALPHA2 parser did not reject a raw lexer-error token"
    case BetaParser.runHolParser [BetaLexer.T_lex_error betaLoc] of
        Left (Just (BetaLexer.T_lex_error _)) -> return ()
        _ -> error "BETA parser did not reject a raw lexer-error token"
