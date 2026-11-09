module Main (main) where

import Control.Monad (forM, unless)
import Control.Monad.IO.Class
import Control.Monad.Trans.Except
import Data.IORef
import Data.List (isInfixOf)
import qualified Data.Map.Strict as Map
import Hol.ALPHA1.Back.Base.TermNode
import Hol.ALPHA1.Back.Base.TermNode.Show ()
import Hol.ALPHA1.Back.Base.VarBinding
import Hol.ALPHA1.Back.Converter.Main
import Hol.ALPHA1.Back.Converter.Util
import Hol.ALPHA1.Back.Runtime.Main
import Hol.ALPHA1.Back.Runtime.Util
import Hol.ALPHA1.Front.Analyzer.Main
import Hol.ALPHA1.Front.Desugarer.ForTerm (isWildCard)
import Hol.ALPHA1.Front.Desugarer.Main
import Hol.ALPHA1.Front.Header
import Hol.ALPHA1.Front.TypeChecker.Main
import Hol.ALPHA1.Main (theInitialFactDecls, theInitialKindDecls, theInitialTypeDecls)
import System.Exit (exitFailure)

assert :: String -> Bool -> IO ()
assert label okay = unless okay (putStrLn ("ALPHA1 regression failed: " ++ label) >> exitFailure)

compileProgram :: String -> UniqueGenT IO (Either ErrMsg (Program TermNode))
compileProgram source = runExceptT $ do
    declarations <- case runAnalyzer source of
        Right (Right declarations) -> return declarations
        Left err -> throwE err
        _ -> throwE "expected a program"
    program <- desugarProgram theInitialKindDecls theInitialTypeDecls "test" declarations
    facts <- forM (_FactDecls program) $ \fact -> do
        (checked, (used, assumptions)) <- checkType (_TypeDecls program) fact mkTyO
        convertProgram used assumptions checked
    return (Program { moduleName = "test", _KindDecls = _KindDecls program, _TypeDecls = _TypeDecls program, _FactDecls = theInitialFactDecls ++ facts })

queryResult :: Program TermNode -> String -> UniqueGenT IO (Either KernelErr [Context])
queryResult program source = do
    (result, answers) <- queryTrace True program source
    case result of
        Left err -> return (Left err)
        Right _ -> return (Right answers)

queryTrace :: Bool -> Program TermNode -> String -> UniqueGenT IO (Either KernelErr Satisfied, [Context])
queryTrace want_more program source = do
    compiled <- runExceptT $ do
        query <- case runAnalyzer source of
            Right (Left query) -> return query
            Left err -> throwE err
            _ -> throwE "expected a query"
        (desugared, variables) <- desugarQuery query
        (checked, (used, assumptions)) <- checkType (_TypeDecls program) desugared mkTyO
        convertQuery used assumptions (mkQueryFreeVariableEnv variables) checked
    case compiled of
        Left err -> liftIO (putStrLn err >> exitFailure)
        Right query -> do
            answers <- liftIO (newIORef [])
            debugging <- liftIO (newIORef False)
            let env = RuntimeEnv { _PutStr = \_ _ -> return True, _Answer = \ctx -> modifyIORef answers (ctx :) >> return want_more }
            result <- runExceptT (execRuntime env debugging (_FactDecls program) query)
            contexts <- liftIO (reverse <$> readIORef answers)
            return (result, contexts)

queryAnswers :: Program TermNode -> String -> UniqueGenT IO [Context]
queryAnswers program source = do
    result <- queryResult program source
    case result of
        Left _ -> liftIO (putStrLn ("ALPHA1 runtime failed: " ++ source) >> exitFailure)
        Right answers -> return answers

isWildVar :: LogicVar -> Bool
isWildVar (LV_Named name) = isWildCard name
isWildVar _ = False

binding :: String -> Context -> Maybe String
binding name ctx = fmap (show . resolveBinding (_TotalVarBinding ctx)) (Map.lookup (LV_Named name) (unVarBinding (_TotalVarBinding ctx)))

main :: IO ()
main = do
    mapM_ (\source -> assert ("unsupported syntax accepted: " ++ source) (either (const True) (const False) (runAnalyzer source))) ["?- X = `true`.", "type P o."]
    mapM_ (\source -> assert ("invalid input accepted: " ++ source) (either (const True) (const False) (runAnalyzer source))) ["?- =.", "?- X = '''.", "?- pi s\\ true."]
    mapM_ (\source -> assert ("old literal/comment rejected: " ++ source) (either (const False) (const True) (runAnalyzer source))) ["?- X = '\"'.", "(***) true.", "(****) true.", "(* ** text *** *) true.", "?- X = \"a\\n\\t\\\\\\\"\\'\"."]
    assert "free variable captured in printed lambda" (show (mkNAbs (mkLVar (LV_Named "W_1"))) == "W_2\\ W_1")
    assert "bare equality has wrong arity" (show (mkNCon DC_Eq) == "W_1\\ W_2\\ W_1 = W_2")
    assert "trailing abstraction is parenthesized" (show (mkNApp (mkNCon LO_pi) (mkNAbs (mkLVar (LV_Named "A")))) == "pi W_1\\ A")
    source <- readFile "test/alpha1/legacy.hol"
    runUniqueGenT $ do
        x <- getNewUnique
        y <- getNewUnique
        captureAvoided <- reduceTermExpr (IApp () (IAbs () x (IAbs () y (IVar () x))) (IVar () y))
        liftIO (assert "beta reduction captured a free variable" (case captureAvoided of
            IAbs _ bound (IVar _ free) -> bound /= y && free == y
            _ -> False))
        shadowed <- reduceTermExpr (IApp () (IAbs () x (IAbs () x (IVar () x))) (IVar () y))
        liftIO (assert "beta reduction substituted through a shadowing binder" (case shadowed of
            IAbs _ bound (IVar _ body) -> bound == body
            _ -> False))
        normalized <- reduceTermExpr (IApp () (IApp () (IAbs () x (IVar () x)) (IAbs () y (IVar () y))) (IVar () x))
        liftIO (assert "beta reduction left a newly exposed redex" (case normalized of
            IVar _ var -> var == x
            _ -> False))
        captureCompiled <- compileProgram "type x (nat -> o). type g (nat -> (nat -> o) -> o). type capture (o -> o). capture ((unused\\ ((f\\ f (f x)) (y\\ z\\ g z y)) 0) 0)."
        captureFacts <- case captureCompiled of
            Left err -> liftIO (putStrLn err >> exitFailure)
            Right facts -> return facts
        captureSuccesses <- mapM (queryAnswers captureFacts)
            [ "?- ((f\\ f (f x)) (y\\ z\\ g z y)) 0 = g 0 (z\\ g z x)."
            , "?- (unused\\ ((f\\ f (f x)) (y\\ z\\ g z y)) 0) 0 = g 0 (z\\ g z x)."
            , "?- capture (g 0 (z\\ g z x))."
            ]
        liftIO (assert "beta-equivalent terms changed across compilation" (all (not . null) captureSuccesses))
        captureFailures <- queryAnswers captureFacts "?- (unused\\ ((f\\ f (f x)) (y\\ z\\ g z y)) 0) 0 = g 0 (z\\ g 0 x)."
        liftIO (assert "beta reduction equated a bound variable with a constant" (null captureFailures))
        mapM_ (\bad -> compileProgram bad >>= liftIO . assert ("invalid clause compiled: " ++ bad) . either (isInfixOf "converting-error") (const False)) ["type p o. p. true.", "type p o. p :- true => p.", "type p o. (p :- true) :- true.", "type p o. type q o. p :- q :- q.", "type p o. 1 = 1.", "type p o. p :- (1 = 1 :- true)."]
        compiled <- compileProgram source
        facts <- case compiled of
            Left err -> liftIO (putStrLn err >> exitFailure)
            Right facts -> return facts
        successes <- mapM (queryAnswers facts) ["?- true.", "?- call true.", "?- store (true => true).", "?- pi (X\\ sigma (Y\\ Y = X)).", "?- pi (X\\ F X = X).", "?- pi (P\\ P => P).", "?- pi X\\ sigma Y\\ Y = X.", "?- X = (Y\\ Y) s.", "?- X = (x\\ x).", "?- pi x\\ sigma Y\\ Y = x.", "?- pi call\\ (call => call)."]
        liftIO (assert "old higher-order or quantified goal failed" (all (not . null) successes))
        failures <- mapM (queryAnswers facts) ["?- fail.", "?- pi (X\\ Y = X).", "?- 1 = 2.", "?- pi x\\ Y = x."]
        liftIO (assert "failure or scope escape succeeded" (all null failures))
        choices <- queryAnswers facts "?- choice N."
        liftIO (assert "backtracking changed" (map (binding "N") choices == [Just "1", Just "2"]))
        cuts <- queryAnswers facts "?- cuttest 3 N."
        liftIO (assert "cut changed" (map (binding "N") cuts == [Just "4"]))
        let deferred = "?- pi p\\ sigma X\\ X = true, (X => (p => p))."
        (stopped, first) <- queryTrace False facts deferred
        liftIO (assert "first answer evaluated a later invalid hypothesis" (case stopped of Right True -> length first == 1; _ -> False))
        (continued, prefix) <- queryTrace True facts deferred
        liftIO (assert "later invalid hypothesis was lost or evaluated before the first answer" (case continued of Left (BadFactGiven _) -> length prefix == 1; _ -> False))
        (immediate, none) <- queryTrace True facts "?- pi p\\ sigma X\\ X = true, (p => (X => p))."
        liftIO (assert "first invalid hypothesis did not error immediately" (case immediate of Left (BadFactGiven _) -> null none; _ -> False))
        cutAnswers <- queryAnswers facts "?- pi p\\ sigma X\\ X = true, (X => (p => (p, !)))."
        liftIO (assert "query cut did not remove a pending invalid hypothesis" (length cutAnswers == 1))
        predicateCut <- queryAnswers facts "?- pi p\\ sigma X\\ X = true, (X => ((p :- !) => p))."
        liftIO (assert "predicate cut did not remove a pending invalid hypothesis" (length predicateCut == 1))
        callerChoices <- queryAnswers facts "?- choice N, (pi p\\ sigma X\\ X = true, (X => ((p :- !) => p)))."
        liftIO (assert "predicate cut removed caller alternatives" (map (binding "N") callerChoices == [Just "1", Just "2"]))
        callerBindings <- queryAnswers facts "?- choice N, cuttest 3 M."
        liftIO (assert "cut lost parent choices or bound variables" (map (binding "N") callerBindings == [Just "1", Just "2"] && map (binding "M") callerBindings == [Just "4", Just "4"]))
        lambdas <- queryAnswers facts "?- X = (x\\ x)."
        liftIO (assert "lower-case binder changed" (map (binding "X") lambdas == [Just "W_1\\ W_1"]))
        kept <- queryAnswers facts "?- X = s (F 1)."
        liftIO (assert "non-pattern subterm deferred" (map (binding "X") kept == [Just "s (F 1)"] && all (null . _LeftConstraints) kept))
        repeated <- queryAnswers facts "?- F = (x\\ G x x)."
        liftIO (assert "repeated-argument subterm deferred" (map (binding "F") repeated == [Just "W_1\\ G W_1 W_1"] && all (null . _LeftConstraints) repeated))
        sums <- queryAnswers facts "?- add 2 3 N."
        liftIO (assert "successor recursion changed" (map (binding "N") sums == [Just "5"]))
        wilds <- queryAnswers facts "?- N = 5, add _ 3 N."
        liftIO (assert "wildcard leaked into the answer" (map (binding "N") wilds == [Just "5"] && all (all (not . isWildVar) . Map.keys . unVarBinding . _TotalVarBinding) wilds))
        forM
            [ ("?- X is 1 + 2 * 3.", "7")
            , ("?- X is (1 + 2) * 3.", "9")
            , ("?- X is 10 - 3 - 2.", "5")
            , ("?- X is 24 // 3 // 2.", "4")
            , ("?- X is 8 / 2.", "4")
            , ("?- X is 7 // 2.", "3")
            , ("?- X is 7 div 2.", "3")
            , ("?- X is 7 mod 2.", "1")
            , ("?- X is 7 rem 2.", "1")
            , ("?- X is +3.", "3")
            , ("?- X is -0.", "0")
            , ("?- X is s 2.", "3")
            , ("?- E = 1 + 2, X is E * 2.", "6")
            , ("?- sigma (Y\\ Y is 3, X is Y + 1).", "4")
            , ("?- X is (Y\\ Y + 1) 2.", "3")
            , ("?- X is 99999999999999999999 * 99999999999999999999.", "9999999999999999999800000000000000000001")
            ] $ \(query, expected) -> do
                answers <- queryAnswers facts query
                liftIO (assert ("wrong arithmetic result: " ++ query) (map (binding "X") answers == [Just expected] && all (null . _LeftConstraints) answers))
        arithmeticTrue <- mapM (queryAnswers facts)
            [ "?- 3 is 1 + 2."
            , "?- 1 + 2 =:= 3."
            , "?- 1 + 2 =\\= 4."
            , "?- 1 < 2, 2 =< 2, 3 > 2, 3 >= 3."
            , "?- 1 + 2 = 1 + 2."
            , "?- pi (P\\ (P :- X is 2 + 3) => P)."
            ]
        liftIO (assert "true arithmetic comparison failed" (all (not . null) arithmeticTrue))
        arithmeticFalse <- mapM (queryAnswers facts)
            [ "?- 1 + 2 is 3."
            , "?- 2 is 1 + 2."
            , "?- 1 + 2 =:= 4."
            , "?- 1 + 2 =\\= 3."
            , "?- 2 < 1."
            , "?- 1 = 1 + 0."
            ]
        liftIO (assert "arithmetic failure or structural equality changed" (all null arithmeticFalse))
        arithmeticChoices <- queryAnswers facts "?- choice N, X is N + 1."
        liftIO (assert "arithmetic lost alternatives or bindings" (map (binding "X") arithmeticChoices == [Just "2", Just "3"]))
        forM
            [ ("?- X is Y + 1.", "instantiation_error")
            , ("?- X is Y * 0.", "instantiation_error")
            , ("?- X is Y / 0.", "instantiation_error")
            , ("?- X < 2.", "instantiation_error")
            , ("?- X =:= X.", "instantiation_error")
            , ("?- X is 1 - 2.", "domain_error(not_less_than_zero")
            , ("?- X is -1.", "domain_error(not_less_than_zero")
            , ("?- X is (1 - 2) * 0.", "domain_error(not_less_than_zero")
            , ("?- X is 7 / 2.", "domain_error(nat")
            , ("?- X is 1 / 0.", "evaluation_error(zero_divisor)")
            , ("?- X is 1 // 0.", "evaluation_error(zero_divisor)")
            , ("?- X is 1 div 0.", "evaluation_error(zero_divisor)")
            , ("?- X is 1 mod 0.", "evaluation_error(zero_divisor)")
            , ("?- X is 1 rem 0.", "evaluation_error(zero_divisor)")
            , ("?- pi (N\\ X is N).", "type_error(evaluable")
            , ("?- X is Y + 1; true.", "instantiation_error")
            ] $ \(query, expected) -> do
                result <- queryResult facts query
                liftIO (assert ("wrong arithmetic error: " ++ query) (case result of
                    Left (ArithmeticFailure err) -> expected `isInfixOf` show err
                    _ -> False))
    putStrLn "ALPHA1 legacy language and bug regressions passed"
