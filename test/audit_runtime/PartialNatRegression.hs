module Main (main) where

import Control.Monad (unless)
import qualified Data.Map.Strict as Map
import qualified Hol.BETA.Arith as Arith
import Hol.BETA.Constant (Constant (..))
import Hol.BETA.Header
import Hol.BETA.HOPU (VarBinding (..), bindVars)
import Hol.BETA.Runtime
import Hol.BETA.TermNode
import Z.Utils (Unique (..))

assert :: String -> Bool -> IO ()
assert label okay = unless okay (error label)

nat :: Integer -> TermNode
nat = mkNCon . DC_NatL

binary :: DataConstructor -> TermNode -> TermNode -> TermNode
binary constructor lhs rhs = mkNApp (mkNApp (mkNCon constructor) lhs) rhs

plus, minus, multiply, divide :: TermNode -> TermNode -> TermNode
plus = binary DC_plus
minus = binary DC_minus
multiply = binary DC_mul
divide = binary DC_div

substitute :: LogicVar -> TermNode -> (TermNode, TermNode) -> (TermNode, TermNode)
substitute variable value (lhs, rhs) =
    let theta = VarBinding (Map.singleton variable value)
    in (bindVars theta lhs, bindVars theta rhs)

main :: IO ()
main = do
    let xVar = LV_Named "X"
        yVar = LV_Named "Y"
        x = mkLVar xVar
        y = mkLVar yVar
        partial = divide x (nat 0)
        erasedPartial = multiply (nat 0) partial
        impossibleUnderflow = minus (nat 0) (plus x (nat 1))

    assert "a known zero denominator must dominate an unknown numerator"
        (evaluateA partial == Left "ill")
    assert "strict multiplication must not erase an ill-defined operand"
        (evaluateA erasedPartial == Left "ill")
    assert "a flexible comparison operand must not hide an ill-defined sibling"
        (evaluateB (mkComparison DC_gt x (divide (nat 1) (nat 0))) == Left "ill")
    assert "symbolic underflow with no valuation must be rejected"
        (not (evaluationConstraintPossible impossibleUnderflow impossibleUnderflow))

    let initiallyDefined = multiply (nat 0) y
        definition = (initiallyDefined, initiallyDefined)
        afterPartialBinding = substitute yVar (divide (nat 1) (nat 0)) definition
    assert "a symbolic strictness obligation remains pending"
        (case recheckEvaluationConstraints [definition] of
            Just [_] -> True
            _ -> False)
    assert "a later HOPU-style partial binding violates that obligation"
        (recheckEvaluationConstraints [afterPartialBinding] == Nothing)

    let delayed = (x, divide y (nat 2))
        afterX = substitute xVar (nat 1) delayed
        solved = substitute yVar (nat 2) afterX
        contradicted = substitute yVar (nat 4) afterX
    assert "binding the lhs must not turn delayed is into another relation"
        (case recheckEvaluationConstraints [afterX] of
            Just [_] -> True
            _ -> False)
    assert "later rhs information completes delayed is"
        (recheckEvaluationConstraints [solved] == Just [])
    assert "later rhs information can refute delayed is"
        (recheckEvaluationConstraints [contradicted] == Nothing)

    let groundedRhs = substitute yVar (nat 2) delayed
    assert "runtime solving turns a newly-ground rhs into an lhs binding"
        (case solveEvaluationConstraints [groundedRhs] of
            Just (VarBinding binding, []) -> Map.lookup xVar binding == Just (nat 1)
            _ -> False)
    let delayedMinus = (x, minus y (nat 1))
        groundedMinus = substitute yVar (nat 2) delayedMinus
    assert "delayed subtraction produces the same lhs binding"
        (case solveEvaluationConstraints [groundedMinus] of
            Just (VarBinding binding, []) -> Map.lookup xVar binding == Just (nat 1)
            _ -> False)

    let bindingChain =
            [ (x, plus y (nat 1))
            , (y, nat 1)
            ]
    assert "delayed evaluation solving is invariant under constraint order"
        (solveEvaluationConstraints bindingChain
            == solveEvaluationConstraints (reverse bindingChain))

    let inconsistentPair =
            [ (x, plus y (nat 1))
            , (x, plus y (nat 2))
            ]
        pairStore =
            [ guardedConstraintStore mempty (EvalutionConstraint lhs rhs)
            | (lhs, rhs) <- inconsistentPair
            ]
    assert "evaluation constraints are checked jointly, not one by one"
        (case sequence pairStore of
            Just guarded -> not (Arith.presburgerGuardedStoreSat guarded)
            Nothing -> False)

    assert "division by a positive literal is universally defined"
        (evaluationConstraintUniversallyValid (divide x (nat 2)) (divide x (nat 2)))
    assert "division by an arbitrary natural is not universally defined"
        (not (evaluationConstraintUniversallyValid (divide (nat 1) x) (divide (nat 1) x)))

    let queryCall = Unique 700
        clauseCall = Unique 701
        leftLoc = SLoc (1, 4) (1, 9)
        rightLoc = SLoc (1, 13) (1, 14)
        wholeLoc = leftLoc <> rightLoc
        locatedLeft = mkNAppLoc (Just leftLoc)
            (mkNAppLoc (Just leftLoc) (mkNConLoc (Just leftLoc) DC_mul) x)
            y
        locatedRight = mkNConLoc (Just rightLoc) (DC_NatL 10)
        located = arithmeticConstraintCandidate
            (Just queryCall) queryCall (DC DC_gt)
            [locatedLeft, locatedRight] [locatedLeft, locatedRight]
        direct = arithmeticConstraintCandidate
            Nothing queryCall (DC DC_gt)
            [locatedLeft, locatedRight] [locatedLeft, locatedRight]
        fromClause = arithmeticConstraintCandidate
            (Just queryCall) clauseCall (DC DC_gt)
            [locatedLeft, locatedRight] [locatedLeft, locatedRight]
    assert "a root-query arithmetic error retains its real source span"
        (getNodeSLoc located == Just wholeLoc)
    assert "a direct Runtime call stays truly locationless"
        (getNodeSLoc direct == Nothing)
    assert "a clause body is not mislabeled with query source lines"
        (getNodeSLoc fromClause == Nothing)

    putStrLn "strict partial-natural runtime regressions passed"
