module Hol.V1.Main where

import qualified Hol.BETA.Main as BETA
import Hol.BETA.Answer (renderAnswer)
import Hol.BETA.Header
import Hol.BETA.HOPU (lookupLVarType)
import Hol.BETA.PlanHolLexer (readHolCharLiteral, readHolStringLiteral)
import Hol.BETA.Runtime
import Hol.BETA.Debugger (initialCache, prettyTerm, recordRename)
import Hol.BETA.Diagnostic (DiagnosticMode (..), diagnosticNoLocWith)
import Hol.BETA.HOPU (VarBinding (..), bindVars, getLVars)
import qualified Hol.BETA.Notation as Notation
import Hol.BETA.TermNode (LogicVar (..), TermNode (..), mkLVar, mkNCon, mkNApp)
import Hol.V1.Bytecode
import Hol.V1.FullBytecode
import qualified Hol.V1.FullRuntime as Full
import qualified Hol.V1.Runtime as Runtime
import Control.Exception (IOException, try)
import Control.Monad
import Control.Monad.IO.Class
import Control.Monad.Trans.Class
import Control.Monad.Trans.Except
import Control.Monad.Trans.Reader (runReaderT)
import Data.IORef
import Data.List (intercalate, nub, stripPrefix)
import Data.Maybe (listToMaybe, mapMaybe)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import System.Exit (exitFailure)
import System.IO (isEOF)
import qualified X.Machine as Native
import qualified Z.Doc as Doc
import Z.System.File (readFileNow)
import Z.System.Shelly
import Z.Utils (Unique (..), UniqueT (..))

validArgs :: [String] -> Bool
validArgs args
    = all validArg args
        && length (nub (map (takeWhile (/= '=')) args)) == length args
        && not ("pretty" `elem` args && "test" `elem` args)
        && not (hasPath "emit-bytecode=" && hasPath "run-bytecode=")
        && not ("general" `elem` args && hasPath "run-bytecode=")
    where
        validArg arg = arg `elem` ["pretty", "test", "strict", "general", "dump-bytecode"]
            || any (maybe False (not . null) . (`stripPrefix` arg)) ["emit-bytecode=", "run-bytecode="]
        hasPath prefix = maybe False (const True) (optionPath prefix args)

optionPath :: String -> [String] -> Maybe FilePath
optionPath prefix = listToMaybe . mapMaybe (stripPrefix prefix)

runtimeRunner :: Bool -> Bool -> BETA.RuntimeRunner
runtimeRunner strict dump = runtimeRunnerWithArtifact strict dump Nothing

runtimeRunnerWithArtifact :: Bool -> Bool -> Maybe FilePath -> BETA.RuntimeRunner
runtimeRunnerWithArtifact strict dump = runtimeRunnerWithOptions False strict dump

runtimeRunnerWithOptions :: Bool -> Bool -> Bool -> Maybe FilePath -> BETA.RuntimeRunner
runtimeRunnerWithOptions forceGeneral strict dump artifact = BETA.RuntimeRunner
    { BETA.runtimeRun = Runtime.execRuntimeWithOptions forceGeneral strict dump artifact
    , BETA.runtimeName = backendName
    }
    where
        backendName = case (forceGeneral, strict) of
            (False, False) -> "V1 bytecode"
            (False, True) -> "V1 bytecode (strict)"
            (True, False) -> "V1 bytecode (general)"
            (True, True) -> "V1 bytecode (general, strict)"

mainWithArgsM :: [String] -> ShellyT ()
mainWithArgsM args
    | not (validArgs args) = do
        shellyM "V1> Usage: V1 [--pretty | --test] [--strict] [--dump-bytecode] [--general] [--emit-bytecode=PATH] or V1 [--pretty | --test] [--dump-bytecode] --run-bytecode=PATH"
        return ()
    | Just path <- optionPath "run-bytecode=" args = liftIO (runBytecodeFile mode dump path)
    | otherwise = BETA.mainWithRunnerM
        (runtimeRunnerWithOptions ("general" `elem` args) ("strict" `elem` args) dump (optionPath "emit-bytecode=" args)) mode
    where
        mode = if "test" `elem` args then DiagnosticTest else DiagnosticPretty
        dump = "dump-bytecode" `elem` args

runBytecodeFile :: DiagnosticMode -> Bool -> FilePath -> IO ()
runBytecodeFile mode dump path = do
    source <- readFileNow path
    case source of
        Nothing -> report ("Cannot read bytecode file `" ++ path ++ "'.")
        Just text -> case deserializeFullBytecode text of
            Right program -> execute (runFullBytecodeProgram dump program)
            Left message
                | take 1 (words text) == ["FullArtifact"] -> report message
            Left _ -> case deserializeBytecode text of
                Left message -> report message
                Right program -> execute (runBytecodeProgram dump program)
    where
        execute action = do
            outcome <- try action :: IO (Either IOException (Either String ()))
            case outcome of
                Left exception -> report (show exception)
                Right (Left message) -> report message
                Right (Right ()) -> return ()
        report message = do
            putStrLn (diagnosticNoLocWith mode "HolV1-BytecodeError" [Doc.text message])
            exitFailure

runFullBytecodeProgram :: Bool -> FullProgram -> IO (Either String ())
runFullBytecodeProgram dump program = case validateFullBytecode program >> ((,) <$> fullUniqueFloor program <*> queryFromBytecode program) of
    Left message -> return (Left message)
    Right (firstUnique, query) -> do
        counter <- newIORef firstUnique
        debugging <- newIORef False
        verbose <- newIORef False
        pending <- newIORef (VarBinding Map.empty)
        stack <- newIORef []
        names <- newIORef initialCache
        answers <- newIORef (0 :: Integer)
        let env = RuntimeEnv
                { _PutStr = interaction
                , _Answer = \context -> case renderAnswer Notation.initial initialCache query context of
                    Nothing -> return True
                    Just lines -> do
                        modifyIORef' answers (+ 1)
                        index <- readIORef answers
                        putStrLn ("HolV1> Answer " ++ show index ++ ".")
                        mapM_ (putStrLn . ("HolV1> " ++)) (if null lines then ["yes."] else lines)
                        return True
                , _PrintPrimitive = \context term -> putStrLn (prettyTerm Notation.initial initialCache (bindVars (_TotalVarBinding context) term) "")
                , _ReadPrimitive = readPrimitive
                , _TypeInfo = fullQueryTypes program
                , _PendingSubst = pending
                , _ProgramKindEnv = fullKindEnv program
                , _ProgramTypeEnv = fullTypeEnv program
                , _VerboseTyping = verbose
                , _StackRef = stack
                , _NameCacheRef = names
                , _DebuggingRef = debugging
                , _NotationDB = Notation.initial
                , _ModuleName = "HolV1"
                , _QueryCallId = Nothing
                }
        when dump (putStr (disassembleFull program))
        outcome <- runReaderT (runUniqueT (runExceptT (Full.runFullProgram env debugging program))) counter
        case outcome of
            Left (BackendError message) -> return (Left message)
            Left (BadGoalGiven term) -> return (Left ("Bad goal: " ++ show term))
            Left (BadFactGiven term) -> return (Left ("Bad fact: " ++ show term))
            Left (UnsupportedArithmeticConstraint term) -> return (Left ("Unsupported arithmetic constraint: " ++ show term))
            Right _ -> putStrLn "HolV1> no." >> return (Right ())
    where
        interaction env _ message = do
            putStrLn message
            ended <- isEOF
            unless ended $ do
                command <- getLine
                case command of
                    ":d" -> runRuntime cmdDebugToggle env
                    _ -> return ()
        readPrimitive context term = do
            ended <- isEOF
            if ended then return Nothing else do
                source <- getLine
                return (parseValue (expectedType context term) source)
        expectedType context term = case bindVars (_TotalVarBinding context) term of
            LVar variable -> lookupLVarType variable (_CurrentLabeling context) `mplus` Map.lookup variable (fullQueryTypes program)
            _ -> Nothing
        parseValue typ source
            | typ == Just mkTyNat = natural source
            | typ == Just mkTyChr = mkNCon . DC_ChrL <$> readHolCharLiteral source
            | typ == Just (mkTyList mkTyChr) = stringTerm <$> readHolStringLiteral source
            | otherwise = natural source `mplus` (mkNCon . DC_ChrL <$> readHolCharLiteral source) `mplus` (stringTerm <$> readHolStringLiteral source)
        natural source
            | not (null source) && all (\ch -> ch >= '0' && ch <= '9') source = case reads source of
                [(value, "")] -> Just (mkNCon (DC_NatL value))
                _ -> Nothing
            | otherwise = Nothing
        stringTerm = foldr cons (mkNApp (mkNCon DC_Nil) charType)
        charType = mkNCon (TC_Named "char")
        cons ch rest = mkNApp (mkNApp (mkNApp (mkNCon DC_Cons) charType) (mkNCon (DC_ChrL ch))) rest

runBytecodeProgram :: Bool -> CompiledProgram -> IO (Either String ())
runBytecodeProgram dump program
    | Left message <- validateBytecode program = return (Left message)
    | otherwise = execute
    where
        execute = case freshStart of
            Nothing -> return (Left "The bytecode query has exhausted the variable identifier space.")
            Just start -> do
                counter <- newIORef start
                when dump (putStr (disassemble program))
                Native.withMachine (bytecodeWords program) $ \machine ->
                    runReaderT (runUniqueT (runExceptT (loop machine 1))) counter
        freshStart
            | largest == maxBound = Nothing
            | otherwise = Just (largest + 1)
            where
                largest = maximum (0 : mapMaybe variableKey (bytecodeVariables program))
        variableKey (LV_ty_var (Unique key)) = Just key
        variableKey (LV_Unique (Unique key) _) = Just key
        variableKey (LV_Named _) = Nothing
        loop :: Native.Machine -> Integer -> ExceptT String (UniqueT IO) ()
        loop machine answerNumber = do
            answer <- liftIO (Native.nextAnswer machine)
            case answer of
                Left message -> throwE message
                Right Nothing -> liftIO (putStrLn "HolV1> no.")
                Right (Just encoded) -> do
                    decoded <- lift (Runtime.decodeAnswer program encoded)
                    binding <- either throwE return decoded
                    liftIO (printBytecodeAnswer answerNumber binding)
                    loop machine (answerNumber + 1)

printBytecodeAnswer :: Integer -> VarBinding -> IO ()
printBytecodeAnswer answerNumber binding = do
    putStrLn ("HolV1> Answer " ++ show answerNumber ++ ".")
    unless (null existentialNames) $
        putStrLn ("HolV1> exists " ++ intercalate ", " existentialNames ++ ".")
    if null answers then
        putStrLn "HolV1> yes."
    else forM_ answers $ \(name, term) ->
        putStrLn ("HolV1> " ++ name ++ " := " ++ prettyTerm Notation.initial cache term ".")
    where
        answers = [(name, bindVars binding term) | (LV_Named name, term) <- Map.toAscList (unVarBinding binding)]
        free = Set.toAscList (getLVars (map snd answers))
        generated = [variable | variable <- free, isGenerated variable]
        usedNames = Set.fromList ([name | (name, _) <- answers] ++ [name | LV_Named name <- free])
        existentialNames = take (length generated)
            [name | n <- [1 :: Integer ..], let name = "E_" ++ show n, name `Set.notMember` usedNames]
        cache = foldl (\current (variable, name) -> recordRename variable name current)
            initialCache (zip generated existentialNames)
        isGenerated (LV_Named _) = False
        isGenerated _ = True

mainWithArgs :: [String] -> IO ()
mainWithArgs = runShellyT . mainWithArgsM

main :: IO ()
main = mainWithArgs []
