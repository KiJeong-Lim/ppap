module Main where

import Control.Monad
import Control.Monad.Trans.Except
import Data.Either (isLeft)
import qualified Data.IntMap.Strict as IntMap
import qualified Data.Map.Strict as Map
import Hol.BETA.Arith (installPresburgerWithEnvDiagnostic)
import Hol.BETA.Compiler (convertQuery)
import Hol.BETA.Desugarer (desugarQuery)
import Hol.BETA.Diagnostic
import Hol.BETA.Header
import Hol.BETA.Main (runAnalyzerWith, theInitialKindDecls, theInitialTypeDecls, theInitialFactDecls)
import Hol.BETA.ModuleLoader
import qualified Hol.BETA.Notation as Notation
import Hol.BETA.TermNode
import Hol.BETA.TypeChecker
import Hol.V1.FullBytecode
import Hol.V1.FullCompiler
import Z.Utils

right :: Either String a -> IO a
right = either (ioError . userError) return

check :: String -> Bool -> IO ()
check label condition = unless condition (ioError (userError label))

query :: ModuleEnv -> String -> UniqueT IO (Either String (TermNode, Map.Map LogicVar (MonoType Int)))
query env source = runExceptT $ do
    parsed <- case runAnalyzerWith DiagnosticTest (moduleEnvNotation env) source of
        Right (Left result) -> return result
        Left message -> throwE message
        _ -> throwE "expected query"
    (desugared, variables) <- desugarQuery (Notation.expandTermRep (moduleEnvExpansion env) parsed)
    (typed, (metas, assumptions)) <- checkTypeWithDiagnostic DiagnosticTest Nothing (moduleEnvNotation env) (moduleEnvTypes env) desugared mkTyO
    let names = Map.fromList [(key, mkLVar (LV_Named name)) | (name, key) <- Map.toList variables]
        freeOf = Map.fromList [(name, term) | (name, key) <- Map.toList variables, Just term <- [Map.lookup key names]]
        types = Map.fromList [(LV_Named name, typ) | (name, key) <- Map.toList variables, Just typ <- [Map.lookup key assumptions]]
    converted <- convertQuery metas assumptions names typed
    installed <- either throwE return (installPresburgerWithEnvDiagnostic DiagnosticTest Nothing Nothing freeOf converted)
    return (installed, types)

main :: IO ()
main = do
    forM_ cases $ \(path, sources) -> do
        loaded <- execUniqueT (loadMainWithDiagnostic DiagnosticTest theInitialKindDecls theInitialTypeDecls theInitialFactDecls path) >>= right
        let env = loadedMain loaded
        forM_ sources $ \source -> do
            (goal, types) <- execUniqueT (query env source) >>= right
            program0 <- right (compileFullProgram (moduleEnvFacts env) goal)
            let program = withRuntimeMetadata (moduleEnvKinds env) (moduleEnvTypes env) types program0
            artifact <- right (serializeFullBytecode program)
            replay <- right (deserializeFullBytecode artifact)
            check "full artifact changed native words" (fullWords program == fullWords replay)
            check "full artifact changed query identity" (fullVariables program == fullVariables replay)
            check "full artifact changed typed metadata" (Map.keys (fullTypeEnv program) == Map.keys (fullTypeEnv replay) && fullQueryTypes program == fullQueryTypes replay)
            restoredGoal <- right (queryFromBytecode replay)
            check "full artifact changed answer projection query" (restoredGoal == goal)
            check "full artifact accepted trailing junk" (isLeft (deserializeFullBytecode (artifact ++ " junk")))
    let arbitrary = 10 ^ (100 :: Int) + 123
        literal = mkNCon (DC_NatL arbitrary)
        equality = foldlNApp (mkNCon DC_eq) [mkNCon (TC_Named "nat"), literal, literal]
    large <- right (compileFullProgram theInitialFactDecls equality)
    _ <- right (serializeFullBytecode large >>= deserializeFullBytecode)
    (header, slots, roles, terms, facts, payload) <- right (fullSections (fullWords large))
    let duplicate = large
            { fullSymbols = IntMap.insert (IntMap.size (fullSymbols large)) (fullSymbols large IntMap.! 0) (fullSymbols large)
            , fullWords = take 3 header ++ [header !! 3 + 1] ++ drop 4 header ++ concat slots ++ roles ++ take 1 roles ++ concat terms ++ concat facts ++ payload
            }
    check "full bytecode accepted duplicate symbol identity" (isLeft (validateFullBytecode duplicate))
    check "full bytecode accepted missing Presburger variable binding" (isLeft (restoreSymbol (SSPresburger (SFRelation 0 (SPVar 1) SPZero) [] Nothing)))
    let open = compileFullProgram [] (mkNIdx 0)
    check "full bytecode accepted an unbound de Bruijn index" (isLeft open)
    putStrLn "Full bytecode compiler: higher-order, dynamic hypotheses, arithmetic, Presburger and artifact metadata passed"
    where
        cases =
            [ ("example/einstein.hol", ["?- answer Houses.", "?- pi x\\ sigma F\\ F x = x.", "?- sigma F\\ pi x\\ F x = x.", "?- pi p\\ p => p.", "?- sigma P\\ P = true, P.", "?- X is 2 * 3.", "?- presburger \"1 < 2\"."])
            , ("example/stlc.hol", ["?- true."])
            ]
