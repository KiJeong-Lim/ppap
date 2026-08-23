module Main where

import Control.Monad (unless)
import Control.Monad.IO.Class (liftIO)
import Control.Monad.Trans.Except
import qualified Data.Map.Strict as Map
import Hol.BETA.Arith (LiftResult (..), liftConstraint, presburgerEntails, presburgerGuardedStoreSat)
import Hol.BETA.Compiler (convertQuery)
import Hol.BETA.Constant (Constant (..))
import Hol.BETA.Desugarer (desugarQuery)
import Hol.BETA.Diagnostic (DiagnosticMode (DiagnosticTest))
import Hol.BETA.Header
import Hol.BETA.Main (runAnalyzerWith, theInitialTypeDecls)
import qualified Hol.BETA.Notation as Notation
import Hol.BETA.Runtime (instantiateArithPremises)
import Hol.BETA.TermNode
import Hol.BETA.TypeChecker (checkTypeWithDiagnostic)
import System.Exit (exitFailure)
import Z.Utils

compileQuery :: String -> IO TermNode
compileQuery source = do
    result <- execUniqueT $ runExceptT $ do
        query1 <- case runAnalyzerWith DiagnosticTest Notation.initial source of
            Right (Left query) -> return query
            Left err -> throwE err
            _ -> throwE "expected a query"
        (query2, freeVars) <- desugarQuery (Notation.expandTermRep Notation.initialExpansionDB query1)
        (query3, (usedMtvs, assumptions)) <- checkTypeWithDiagnostic DiagnosticTest (Just (lines source)) Notation.initial theInitialTypeDecls query2 mkTyO
        let freeVarEnv = Map.fromList [ (ivar, mkLVar (LV_Named name)) | (name, ivar) <- Map.toList freeVars ]
        convertQuery usedMtvs assumptions freeVarEnv query3
    case result of
        Left err -> putStrLn err >> exitFailure
        Right query -> return query

main :: IO ()
main = do
    query <- compileQuery "?- pi C\\ (C > 3 => C < 2)."
    let rigid = mkNCon (DC_Unique (Unique 1000) noHint)
        instantiated = case unfoldlNApp query of
            (NCon (DC (DC_LO LO_pi)) _, [lambda]) -> rewrite HNF (mkNApp lambda rigid)
            _ -> error "compiled query did not have a pi head"
        consequent = case unfoldlNApp instantiated of
            (NCon (DC (DC_LO LO_imply)) _, [_, goal]) -> goal
            _ -> error "compiled pi body did not have an implication head"
    case liftConstraint consequent of
        Just _ -> putStrLn "linear bound/rigid arithmetic lifting passed"
        Nothing -> do
            liftIO (putStrLn "linear rigid comparison was rejected")
            exitFailure

    quantifiedQuery <- compileQuery "?- ((pi C\\ C > 3) => 5 > 100)."
    case unfoldlNApp quantifiedQuery of
        (NCon (DC (DC_LO LO_imply)) _, [antecedent, goal]) -> do
            premises <- execUniqueT (instantiateArithPremises antecedent)
            case liftConstraint goal of
                Just lifted -> unless (presburgerEntails premises (_liftedFormula lifted, _freeOfLifted lifted)) $ do
                    putStrLn "antecedent-local pi was not retained as a universal arithmetic premise"
                    exitFailure
                Nothing -> putStrLn "quantified regression goal did not lift" >> exitFailure
        _ -> putStrLn "quantified regression query did not have an implication head" >> exitFailure

    let x = mkLVar (LV_Named "X")
        nat n = mkNCon (DC_NatL n)
        natEq lhs rhs = mkNApp (mkNApp (mkNApp (mkNCon DC_eq) (mkNCon (TC_Named "nat"))) lhs) rhs
        jointlyImpossible =
            [ (([], []), ([natEq x (nat 0)], []))
            , (([], []), ([natEq x (nat 1)], []))
            ]
    unless (not (presburgerGuardedStoreSat jointlyImpossible)) $ do
        putStrLn "guarded residuals were closed separately instead of sharing the query variable"
        exitFailure
    putStrLn "quantified premise/guarded residual regressions passed"
