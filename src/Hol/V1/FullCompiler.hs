module Hol.V1.FullCompiler (compileFullProgram, PreparedProgram, prepareFullProgram, compilePreparedProgram, LoadedTables, loadPreparedProgram, extendLoadedProgram, queryLoadedProgram, validateLoadedFragment, fragmentIndices, loadedSourceTerms) where

import Control.Monad
import Control.Monad.Trans.Class
import Control.Monad.Trans.State.Strict
import Data.Char (ord)
import Data.Int
import qualified Data.IntMap.Strict as IntMap
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Hol.BETA.Constant
import Hol.BETA.Header
import Hol.BETA.HOPU (getLVars)
import Hol.BETA.Runtime (expandAssumptions)
import Hol.BETA.TermNode
import Hol.V1.Bytecode (bytecodeMagic)
import Hol.V1.FullBytecode

-- The tag, the two operands and the metadata of a template row.
data TermKey
    = TermKey !Int64 !Int64 !Int64 !Int64
    deriving (Eq, Ord)

data Build
    = Build
        { builtTerms :: IntMap.IntMap [Int64]
        , termKeys :: Map.Map TermKey Int
        , builtSymbols :: IntMap.IntMap FullSymbol
        , symbolKeys :: Map.Map String Int
        , constantKeys :: Map.Map Constant Int
        , builtMetadata :: IntMap.IntMap NodeMetadata
        , metadataKeys :: Map.Map (Maybe String, Maybe StoredType, Maybe ((Int, Int), (Int, Int))) Int
        , digitPayload :: [Int64]
        , digitCount :: Int
        , literalKeys :: Map.Map String (Int, Int)
        , variableSlots :: Map.Map LogicVar Int
        }
    deriving ()

-- Each key map has one entry for every row of its table, so its size, which
-- is known without a traversal, is the index of the next row.
type Compile = StateT Build (Either String)

-- Facts that are compiled already. A query and further facts are compiled on
-- top of them (compilePreparedProgram), so their cost is paid once.
data PreparedProgram
    = PreparedProgram
        { preparedBuild :: Build
        , preparedFacts :: [[Int64]]
        , preparedKinds :: KindEnv
        , preparedTypes :: TypeEnv
        }
    deriving ()

-- The symbols and annotations of a program that a machine holds. Fragments are
-- compiled against them: they number their own templates, clauses and digits
-- from zero, and add to these two tables only.
data LoadedTables
    = LoadedTables
        { loadedBuild :: Build
        , loadedKinds :: KindEnv
        , loadedTypes :: TypeEnv
        }
    deriving ()

compileFullProgram :: [TermNode] -> TermNode -> Either String FullProgram
compileFullProgram facts query = assertNonnegativeTerms (query : facts) `seq` do
    let expanded = concatMap expandAssumptions facts
        variables = Set.toAscList (getLVars (query : expanded))
    ((slots, root, clauses), built) <- runStateT (internBuiltins >> compileQuery variables query expanded) (emptyBuild { variableSlots = Map.fromList (zip variables [0 ..]) })
    let program = assemble 0 built variables slots root clauses
    validateFullBytecode program
    return program

-- The facts have no logic variable. The symbols of the two environments are
-- interned here, as withRuntimeMetadata adds them to a compiled program.
prepareFullProgram :: KindEnv -> TypeEnv -> [TermNode] -> Either String PreparedProgram
prepareFullProgram kinds types facts = assertNonnegativeTerms facts `seq` do
    let expanded = concatMap expandAssumptions facts
    unless (Set.null (getLVars expanded)) (Left "a prepared fact has a logic variable")
    (clauses, built) <- runStateT (internBuiltins >> mapM compileFact expanded <* mapM_ (internSymbol . ConstantSymbol) (map TC (Map.keys kinds) ++ map DC (Map.keys types))) emptyBuild
    return (PreparedProgram built clauses kinds types)

-- compilePreparedProgram (prepareFullProgram kinds types facts0) queryTypes facts1 query runs like
-- withRuntimeMetadata kinds types queryTypes applied to compileFullProgram (facts0 ++ facts1) query.
-- The program is not validated here: createSession validates every program it runs.
compilePreparedProgram :: PreparedProgram -> Map.Map LogicVar (MonoType Int) -> [TermNode] -> TermNode -> Either String FullProgram
compilePreparedProgram prepared queryTypes facts query = assertNonnegativeTerms (query : facts) `seq` do
    let expanded = concatMap expandAssumptions facts
        variables = Set.toAscList (getLVars (query : expanded))
    ((slots, root, clauses), built) <- runStateT (compileQuery variables query expanded) ((preparedBuild prepared) { variableSlots = Map.fromList (zip variables [0 ..]) })
    return (assemble 0 built variables slots root (preparedFacts prepared ++ clauses)) { fullKindEnv = preparedKinds prepared, fullTypeEnv = preparedTypes prepared, fullQueryTypes = queryTypes }

-- The whole prepared program with the query `true`, for hol_v2_create, and its
-- tables. A machine created from it has no query variable.
loadPreparedProgram :: PreparedProgram -> Either String (FullProgram, LoadedTables)
loadPreparedProgram prepared = do
    ((slots, root, clauses), built) <- runStateT (compileQuery [] (mkNCon (DC_LO LO_true)) []) (preparedBuild prepared)
    let program = (assemble 0 built [] slots root (preparedFacts prepared ++ clauses)) { fullKindEnv = preparedKinds prepared, fullTypeEnv = preparedTypes prepared }
    return (program, LoadedTables (withoutTemplates built) (preparedKinds prepared) (preparedTypes prepared))

-- A fragment that adds facts without a logic variable, and the tables after it.
extendLoadedProgram :: LoadedTables -> [TermNode] -> Either String (FullProgram, LoadedTables)
extendLoadedProgram tables facts = assertNonnegativeTerms facts `seq` do
    let expanded = concatMap expandAssumptions facts
    unless (Set.null (getLVars expanded)) (Left "a loaded fact has a logic variable")
    (clauses, built) <- runStateT (mapM compileFact expanded) (loadedBuild tables)
    let program = (assemble (knownSymbols tables) built [] [] (-1) clauses) { fullKindEnv = loadedKinds tables, fullTypeEnv = loadedTypes tables }
    return (program, tables { loadedBuild = withoutTemplates built })

-- A fragment with a query. What it adds to the tables lasts for its run.
queryLoadedProgram :: LoadedTables -> Map.Map LogicVar (MonoType Int) -> TermNode -> Either String FullProgram
queryLoadedProgram tables queryTypes query = assertNonnegativeTerms [query] `seq` do
    let variables = Set.toAscList (getLVars query)
    ((slots, root, _), built) <- runStateT (compileQuery variables query []) ((loadedBuild tables) { variableSlots = Map.fromList (zip variables [0 ..]) })
    return (assemble (knownSymbols tables) built variables slots root []) { fullKindEnv = loadedKinds tables, fullTypeEnv = loadedTypes tables, fullQueryTypes = queryTypes }

-- A fragment compiled against `tables` is validated against them.
validateLoadedFragment :: LoadedTables -> FullProgram -> Either String ()
validateLoadedFragment tables = validateFullFragment (`Map.member` symbolKeys (loadedBuild tables)) (knownSymbols tables) (Map.size (metadataKeys (loadedBuild tables)))

-- The index of every symbol of a fragment compiled against `tables`, by identity.
fragmentIndices :: LoadedTables -> FullProgram -> Map.Map String Int
fragmentIndices tables program = IntMap.foldlWithKey' (\indices index symbol -> Map.insert (symbolIdentity symbol) index indices) (symbolKeys (loadedBuild tables)) (snd (IntMap.split (knownSymbols tables - 1) (fullSymbols program)))

-- The clauses and the query of a fragment compiled against `tables`.
loadedSourceTerms :: LoadedTables -> FullProgram -> Either String ([TermNode], Maybe TermNode)
loadedSourceTerms tables program = validateLoadedFragment tables program >> fragmentSourceTerms (knownSymbols tables) program

knownSymbols :: LoadedTables -> Int
knownSymbols = Map.size . symbolKeys . loadedBuild

withoutTemplates :: Build -> Build
withoutTemplates built = built { builtTerms = IntMap.empty, termKeys = Map.empty, digitPayload = [], digitCount = 0, literalKeys = Map.empty, variableSlots = Map.empty }

emptyBuild :: Build
emptyBuild = Build IntMap.empty Map.empty IntMap.empty Map.empty Map.empty IntMap.empty Map.empty [] 0 Map.empty Map.empty

-- Natural literal views need the successor symbol even when no explicit
-- successor appears in the source.
internBuiltins :: Compile ()
internBuiltins = mapM_ (internSymbol . ConstantSymbol) (map (DC . DC_LO) logicalOperators ++ builtinConstants ++ [DC (DC_Named "read"), DC (DC_Named "print"), DC (DC_Named "flex")])

compileQuery :: [LogicVar] -> TermNode -> [TermNode] -> Compile ([[Int64]], Int, [[Int64]])
compileQuery variables query expanded = do
    slots <- mapM querySlot variables
    root <- compileTerm query
    clauses <- mapM compileFact expanded
    return (slots, root, clauses)
    where
        querySlot variable = do
            meta <- internMetadata (NodeMetadata (variableHint variable) noLamType Nothing)
            return [if isTypeVariable variable then 1 else 0, fromIntegral meta]
        variableHint (LV_Unique _ (DispHint hint)) = hint
        variableHint _ = Nothing
        isTypeVariable (LV_ty_var _) = True
        isTypeVariable _ = False

-- The symbol section has the roles of the symbols from `known` on. The sizes
-- of the key maps are the counts: they are known without a traversal.
assemble :: Int -> Build -> [LogicVar] -> [[Int64]] -> Int -> [[Int64]] -> FullProgram
assemble known built variables slots root clauses = FullProgram words (builtSymbols built) variables (builtMetadata built) Map.empty Map.empty Map.empty where
    header = [bytecodeMagic, 2, fromIntegral (Map.size (termKeys built)), fromIntegral (Map.size (symbolKeys built)), fromIntegral (length clauses), fromIntegral (length variables), fromIntegral root, fromIntegral (Map.size (metadataKeys built))]
    words = header ++ concat slots ++ map (fromIntegral . symbolRole) (IntMap.elems (snd (IntMap.split (known - 1) (builtSymbols built)))) ++ concat (IntMap.elems (builtTerms built)) ++ concat clauses ++ reverse (digitPayload built)

compileFact :: TermNode -> Compile [Int64]
compileFact fact = do
    root <- compileTerm fact
    predicate <- case factHead fact of
        Just constant -> internSymbol (ConstantSymbol constant)
        Nothing -> return (-1)
    return [fromIntegral predicate, fromIntegral root]
    where
        factHead term = case unfoldlNApp (rewrite HNF term) of
            (NCon (DC (DC_LO operator)) _, [NLam _ _ body _])
                | operator == LO_ty_pi || operator == LO_pi -> factHead body
            (NCon (DC (DC_LO LO_if)) _, [headTerm, _]) -> factHead headTerm
            (NCon constant _, _) -> Just constant
            _ -> Nothing

compileTerm :: TermNode -> Compile Int
compileTerm term = case term of
    LVar variable -> do
        slots <- gets variableSlots
        case Map.lookup variable slots of
            Just slot -> internTerm 0 (fromIntegral slot) 0 (-1)
            Nothing -> lift (Left "unregistered full bytecode variable")
    NCon (DC (DC_NatL value)) location -> do
        (offset, count) <- internNatural value
        meta <- sourceMetadata location
        internTerm 5 (fromIntegral offset) (fromIntegral count) (fromIntegral meta)
    NCon (DC DC_wc) location -> do
        meta <- sourceMetadata location
        internTerm 6 0 0 (fromIntegral meta)
    NCon constant location -> do
        symbol <- internSymbol (ConstantSymbol constant)
        meta <- sourceMetadata location
        internTerm 1 (fromIntegral symbol) 0 (fromIntegral meta)
    NIdx index -> internTerm 3 (fromIntegral index) 0 (-1)
    NApp function argument location -> do
        function' <- compileTerm function
        argument' <- compileTerm argument
        meta <- sourceMetadata location
        internTerm 2 (fromIntegral function') (fromIntegral argument') (fromIntegral meta)
    NLam hint typ body location -> do
        body' <- compileTerm body
        meta <- internMetadata (NodeMetadata hint typ location)
        internTerm 4 (fromIntegral body') 0 (fromIntegral meta)
    suspended@Susp {} -> compileTerm (rewrite NF suspended)
    NPresburgerCheck formula freeOf location -> do
        symbol <- internSymbol (PresburgerSymbol formula (Map.keys freeOf) location)
        meta <- sourceMetadata location
        headRoot <- internTerm 1 (fromIntegral symbol) 0 (fromIntegral meta)
        foldM (apply meta) headRoot (Map.elems freeOf)
    where
        apply meta function argument = do
            argument' <- compileTerm argument
            internTerm 2 (fromIntegral function) (fromIntegral argument') (fromIntegral meta)

sourceMetadata :: Maybe SLoc -> Compile Int
sourceMetadata Nothing = return (-1)
sourceMetadata location = internMetadata (NodeMetadata Nothing noLamType location)

internMetadata :: NodeMetadata -> Compile Int
internMetadata meta = do
    let key = storeMetadata meta
    known <- gets (Map.lookup key . metadataKeys)
    case known of
        Just index -> return index
        Nothing -> do
            index <- gets (Map.size . metadataKeys)
            modify (\state -> state { builtMetadata = IntMap.insert index meta (builtMetadata state), metadataKeys = Map.insert key index (metadataKeys state) })
            return index

-- The identity of a symbol is a string. A constant that was seen before is
-- found without building it again.
internSymbol :: FullSymbol -> Compile Int
internSymbol symbol = case symbol of
    ConstantSymbol constant -> do
        seen <- gets (Map.lookup constant . constantKeys)
        case seen of
            Just index -> return index
            Nothing -> do
                index <- internIdentity symbol
                modify (\state -> state { constantKeys = Map.insert constant index (constantKeys state) })
                return index
    _ -> internIdentity symbol

internIdentity :: FullSymbol -> Compile Int
internIdentity symbol = do
    let key = symbolIdentity symbol
    known <- gets (Map.lookup key . symbolKeys)
    case known of
        Just index -> return index
        Nothing -> do
            index <- gets (Map.size . symbolKeys)
            modify (\state -> state { builtSymbols = IntMap.insert index symbol (builtSymbols state), symbolKeys = Map.insert key index (symbolKeys state) })
            return index

internTerm :: Int64 -> Int64 -> Int64 -> Int64 -> Compile Int
internTerm tag a b meta = do
    let key = TermKey tag a b meta
    known <- gets (Map.lookup key . termKeys)
    case known of
        Just index -> return index
        Nothing -> do
            index <- gets (Map.size . termKeys)
            modify (\state -> state { builtTerms = IntMap.insert index [tag, a, b, 0, 0, meta] (builtTerms state), termKeys = Map.insert key index (termKeys state) })
            return index

internNatural :: Integer -> Compile (Int, Int)
internNatural value
    | value < 0 = lift (Left "negative natural in full bytecode")
    | otherwise = do
        let digits = show value
        known <- gets (Map.lookup digits . literalKeys)
        case known of
            Just entry -> return entry
            Nothing -> do
                offset <- gets digitCount
                let count = length digits
                    entry = (offset, count)
                modify (\state -> state { digitPayload = reverse (map (fromIntegral . ord) digits) ++ digitPayload state, digitCount = offset + count, literalKeys = Map.insert digits entry (literalKeys state) })
                return entry
