module Hol.V1.Runtime where

import Control.Exception (IOException, onException, try)
import Control.Monad
import Control.Monad.IO.Class
import Control.Monad.Trans.Class
import Control.Monad.Trans.Except
import Control.Monad.Trans.State.Strict
import Data.Int
import Data.IORef
import qualified Data.IntMap.Strict as IntMap
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Hol.BETA.Constant
import Hol.BETA.Header
import Hol.BETA.HOPU
import Hol.BETA.Runtime
import Hol.BETA.TermNode
import qualified Hol.BETA.TypeChecker as TypeChecker
import Hol.V1.Bytecode
import Hol.V1.Compiler
import Hol.V1.FullBytecode
import Hol.V1.FullCompiler
import qualified Hol.V1.FullRuntime as Full
import qualified X.Machine as Native
import Z.Utils

execRuntime :: UniqueM m => RuntimeEnv -> IORef Bool -> [Fact] -> Goal -> ExceptT KernelErr m Satisfied
execRuntime env debugging facts query = do
    compiled <- either (throwE . BackendError) return (compileFullProgram facts query)
    let program = withRuntimeMetadata (_ProgramKindEnv env) (_ProgramTypeEnv env) (_TypeInfo env) compiled
    Full.runFullProgram (env { _QueryCallId = Just (Unique 0) }) debugging program

execRuntimeWith :: UniqueM m => Bool -> Bool -> RuntimeEnv -> IORef Bool -> [Fact] -> Goal -> ExceptT KernelErr m Satisfied
execRuntimeWith strict dump = execRuntimeWithArtifact strict dump Nothing

execRuntimeWithArtifact :: UniqueM m => Bool -> Bool -> Maybe FilePath -> RuntimeEnv -> IORef Bool -> [Fact] -> Goal -> ExceptT KernelErr m Satisfied
execRuntimeWithArtifact strict dump = execRuntimeWithOptions False strict dump

execRuntimeWithOptions :: UniqueM m => Bool -> Bool -> Bool -> Maybe FilePath -> RuntimeEnv -> IORef Bool -> [Fact] -> Goal -> ExceptT KernelErr m Satisfied
execRuntimeWithOptions forceGeneral _strict dump artifact env debugging facts query = do
    activeDebug <- liftIO (readIORef debugging)
    pending <- liftIO (readIORef (_PendingSubst env))
    if forceGeneral || activeDebug then
        fullRuntime
    else if not (Map.null (unVarBinding pending)) then
        fullRuntime
    else case compileProgram facts query of
        Left _ -> fullRuntime
        Right program -> do
            when dump (liftIO (putStr (disassemble program)))
            forM_ artifact $ \path -> do
                encoded <- either (throwE . BackendError) return (serializeBytecode program)
                written <- liftIO (try (writeFile path encoded) :: IO (Either IOException ()))
                either (throwE . BackendError . show) return written
            runCompiled env debugging program
    where
        fullRuntime = do
            compiled <- either (throwE . BackendError) return (compileFullProgram facts query)
            let program = withRuntimeMetadata (_ProgramKindEnv env) (_ProgramTypeEnv env) (_TypeInfo env) compiled
            when dump (liftIO (putStr (disassembleFull program)))
            forM_ artifact $ \path -> do
                encoded <- either (throwE . BackendError) return (serializeFullBytecode program)
                written <- liftIO (try (writeFile path encoded) :: IO (Either IOException ()))
                either (throwE . BackendError . show) return written
            Full.runFullProgram (env { _QueryCallId = Just (Unique 0) }) debugging program

-- Native answers cross into the existing presentation layer only at yields.
-- Interactive debugging and native snapshots use FullRuntime.
runCompiled :: UniqueM m => RuntimeEnv -> IORef Bool -> CompiledProgram -> ExceptT KernelErr m Satisfied
runCompiled env debugging program = do
    either (throwE . BackendError) return (validateBytecode program)
    callId <- getUnique
    opened <- liftIO (openMachine (bytecodeWords program))
    machine <- either (throwE . BackendError . show) return opened
    result <- lift (runExceptT (loop machine callId))
    liftIO (Native.closeMachine machine)
    either throwE return result
    where
        openMachine :: [Int64] -> IO (Either IOException Native.Machine)
        openMachine = try . Native.createMachine
        loop machine callId = do
            result <- liftIO (Native.nextAnswer machine `onException` Native.closeMachine machine)
            case result of
                Left reason -> throwE (BackendError reason)
                Right Nothing -> return False
                Right (Just encoded) -> do
                    decoded <- lift (decodeAnswer program encoded)
                    binding <- either (throwE . BackendError) return decoded
                    let context = Context
                            { _TotalVarBinding = binding
                            , _CurrentLabeling = labelAnswer env binding
                            , _LeftConstraints = []
                            , _ContextThreadId = callId
                            , _debuggindModeOn = debugging
                            }
                    more <- liftIO (_Answer env context `onException` Native.closeMachine machine)
                    if more then do
                        activeDebug <- liftIO (readIORef debugging)
                        pending <- liftIO (readIORef (_PendingSubst env))
                        when (activeDebug || not (Map.null (unVarBinding pending))) (throwE (BackendError "V1 native answer callbacks cannot enable debugging or assign variables during a search"))
                        loop machine callId
                    else
                        return True

-- Propagate only exact type evidence.  An unrecognized constructor, missing
-- type argument, unresolved type or conflicting occurrence contributes no
-- guessed label to the answer callback.
inferAnswerTypes :: KindEnv -> TypeEnv -> Map.Map LogicVar (MonoType Int) -> VarBinding -> Map.Map LogicVar (MonoType Int)
inferAnswerTypes kindEnv typeEnv queryTypes (VarBinding binding)
    = Map.mapMaybe id (Map.fromListWith agree evidence)
    where
        known = Map.filter exactType queryTypes
        evidence = [(variable, Just typ) | (variable, typ) <- Map.toList known]
            ++ [(variable, Just typ) | (variable, typ) <- inferred]
        inferred = concat
            [ maybe [] id (collect (Set.singleton variable) typ value)
            | (variable, value) <- Map.toList binding
            , Just typ <- [Map.lookup variable known]
            ]
        agree (Just lhs) (Just rhs)
            | TypeChecker.typesAgreeIncludingKinds lhs rhs = Just lhs
        agree _ _ = Nothing

        exactType typ = closed typ && case TypeChecker.getKindEither typ of
            Right Star -> True
            _ -> False
        closed (TyCon _) = True
        closed (TyApp lhs rhs) = closed lhs && closed rhs
        closed _ = False

        collect seen expected value
            | not (exactType expected) = Nothing
            | otherwise = case value of
                LVar variable -> do
                    nested <- case Map.lookup variable binding of
                        Just other
                            | variable `Set.notMember` seen ->
                                collect (Set.insert variable seen) expected other
                        _ -> Just []
                    return ((variable, expected) : nested)
                _ -> do
                    (arguments, domains, resultType) <- constructorType value
                    guard (TypeChecker.typesAgreeIncludingKinds expected resultType)
                    concat <$> zipWithM (collect seen) domains arguments

        constructorType value = case unfoldlNApp value of
            (NCon (DC constructor) _, arguments) -> do
                Forall parameters body <- constructorScheme constructor
                let (typeArguments, valueArguments) = splitAt (length parameters) arguments
                guard (length typeArguments == length parameters)
                replacements <- mapM (primitiveTypeArgumentWithKinds kindEnv) typeArguments
                guard (all exactType replacements)
                signature <- substituteType replacements body
                guard (exactType signature)
                (domains, resultType) <- splitArrowsHOPU (length valueArguments) signature
                return (valueArguments, domains, resultType)
            _ -> Nothing
        constructorScheme (DC_NatL value)
            | value >= 0 = Just (Forall [] mkTyNat)
            | otherwise = Nothing
        constructorScheme (DC_ChrL _) = Just (Forall [] mkTyChr)
        constructorScheme constructor = Map.lookup constructor typeEnv

        substituteType replacements typ = case typ of
            TyVar index
                | index >= 0 -> atIndex index replacements
                | otherwise -> Nothing
            TyCon constructor -> Just (TyCon constructor)
            TyApp lhs rhs -> TyApp <$> substituteType replacements lhs <*> substituteType replacements rhs
            TyMTV _ -> Nothing
        atIndex _ [] = Nothing
        atIndex 0 (typ : _) = Just typ
        atIndex index (_ : rest) = atIndex (index - 1) rest

labelAnswer :: RuntimeEnv -> VarBinding -> Labeling
labelAnswer env binding = Labeling
    { _ConLabel = IntMap.empty
    , _VarLabel = IntMap.fromList [(lvKey variable, 0) | variable <- generated]
    , _ConTypes = IntMap.empty
    , _VarTypes = IntMap.fromList
        [(lvKey variable, typ) | (variable, typ) <- Map.toList inferred, isGenerated variable]
    , _NamedTypes = Map.fromList [(name, typ) | (LV_Named name, typ) <- Map.toList (_TypeInfo env)]
    , _TyVarKeys = IntMap.empty
    , _TypeEnv = _ProgramTypeEnv env
    }
    where
        inferred = inferAnswerTypes (_ProgramKindEnv env) (_ProgramTypeEnv env) (_TypeInfo env) binding
        generated = Set.toList $ Set.filter isGenerated (getLVars (Map.elems (unVarBinding binding)) `Set.union` Map.keysSet inferred)
        isGenerated (LV_Named _) = False
        isGenerated _ = True

decodeAnswer :: MonadUnique m => CompiledProgram -> [Int64] -> m (Either String VarBinding)
decodeAnswer program words0 = runExceptT $ do
    (values, (remaining, _)) <- runStateT (replicateM (bytecodeQuerySlots program) term) (words0, queryNames)
    unless (null remaining) (throwE "V1 bytecode: trailing words in an answer")
    return (VarBinding (Map.fromList [(var, value) | (var, value) <- zip (bytecodeVariables program) values, value /= mkLVar var]))
    where
        queryNames = Map.fromList (zip [0 ..] (bytecodeVariables program))
        word = do
            (remaining, names) <- get
            case remaining of
                [] -> lift (throwE "V1 bytecode: truncated answer")
                value : rest -> put (rest, names) >> return value
        term = do
            tag <- word
            case tag of
                0 -> do
                    ident <- word
                    when (ident < 0) (lift (throwE "V1 bytecode: negative variable identifier"))
                    (_, names) <- get
                    case Map.lookup ident names of
                        Just var -> return (mkLVar var)
                        Nothing -> do
                            var <- fmap (\unique -> LV_Unique unique noHint) getUnique
                            modify (\(rest, old) -> (rest, Map.insert ident var old))
                            return (mkLVar var)
                1 -> do
                    ident <- word
                    if ident < 0 || toInteger ident > toInteger (maxBound :: Int) then
                        lift (throwE "V1 bytecode: invalid constant identifier")
                    else case IntMap.lookup (fromIntegral ident) (bytecodeConstants program) of
                        Nothing -> lift (throwE "V1 bytecode: unknown constant identifier")
                        Just constant -> return (mkNCon constant)
                2 -> mkNApp <$> term <*> term
                _ -> lift (throwE "V1 bytecode: invalid answer tag")
