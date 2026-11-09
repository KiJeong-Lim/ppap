module Hol.V1.FullCompiler (compileFullProgram) where

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

data Build
    = Build
        { builtTerms :: IntMap.IntMap [Int64]
        , termKeys :: Map.Map [Int64] Int
        , builtSymbols :: IntMap.IntMap FullSymbol
        , symbolKeys :: Map.Map String Int
        , builtMetadata :: IntMap.IntMap NodeMetadata
        , metadataKeys :: Map.Map (Maybe String, Maybe StoredType, Maybe ((Int, Int), (Int, Int))) Int
        , digitPayload :: [Int64]
        , digitCount :: Int
        , literalKeys :: Map.Map String (Int, Int)
        , variableSlots :: Map.Map LogicVar Int
        }
    deriving ()

type Compile = StateT Build (Either String)

compileFullProgram :: [TermNode] -> TermNode -> Either String FullProgram
compileFullProgram facts query = assertNonnegativeTerms (query : facts) `seq` do
    let expanded = concatMap expandAssumptions facts
        variables = Set.toAscList (getLVars (query : expanded))
        initial = Build IntMap.empty Map.empty IntMap.empty Map.empty IntMap.empty Map.empty [] 0 Map.empty (Map.fromList (zip variables [0 ..]))
    ((slots, root, clauses), built) <- runStateT (build variables expanded) initial
    let header = [bytecodeMagic, 2, fromIntegral (IntMap.size (builtTerms built)), fromIntegral (IntMap.size (builtSymbols built)), fromIntegral (length clauses), fromIntegral (length variables), fromIntegral root, fromIntegral (IntMap.size (builtMetadata built))]
        words = header ++ concat slots ++ map (fromIntegral . symbolRole) (IntMap.elems (builtSymbols built)) ++ concat (IntMap.elems (builtTerms built)) ++ concat clauses ++ reverse (digitPayload built)
        program = FullProgram words (builtSymbols built) variables (builtMetadata built) Map.empty Map.empty Map.empty
    validateFullBytecode program
    return program
    where
        build variables expanded = do
            -- Natural literal views need the successor symbol even when no
            -- explicit successor appears in the source.
            mapM_ (internSymbol . ConstantSymbol) (map (DC . DC_LO) logicalOperators ++ builtinConstants ++ [DC (DC_Named "read"), DC (DC_Named "print")])
            slots <- mapM querySlot variables
            root <- compileTerm query
            clauses <- mapM compileFact expanded
            return (slots, root, clauses)
        querySlot variable = do
            meta <- internMetadata (NodeMetadata (variableHint variable) noLamType Nothing)
            return [if isTypeVariable variable then 1 else 0, fromIntegral meta]
        variableHint (LV_Unique _ (DispHint hint)) = hint
        variableHint _ = Nothing
        isTypeVariable (LV_ty_var _) = True
        isTypeVariable _ = False

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
            Just slot -> internTerm [0, fromIntegral slot, 0, 0, 0, -1]
            Nothing -> lift (Left "unregistered full bytecode variable")
    NCon (DC (DC_NatL value)) location -> do
        (offset, count) <- internNatural value
        meta <- sourceMetadata location
        internTerm [5, fromIntegral offset, fromIntegral count, 0, 0, fromIntegral meta]
    NCon (DC DC_wc) location -> do
        meta <- sourceMetadata location
        internTerm [6, 0, 0, 0, 0, fromIntegral meta]
    NCon constant location -> do
        symbol <- internSymbol (ConstantSymbol constant)
        meta <- sourceMetadata location
        internTerm [1, fromIntegral symbol, 0, 0, 0, fromIntegral meta]
    NIdx index -> internTerm [3, fromIntegral index, 0, 0, 0, -1]
    NApp function argument location -> do
        function' <- compileTerm function
        argument' <- compileTerm argument
        meta <- sourceMetadata location
        internTerm [2, fromIntegral function', fromIntegral argument', 0, 0, fromIntegral meta]
    NLam hint typ body location -> do
        body' <- compileTerm body
        meta <- internMetadata (NodeMetadata hint typ location)
        internTerm [4, fromIntegral body', 0, 0, 0, fromIntegral meta]
    suspended@Susp {} -> compileTerm (rewrite NF suspended)
    NPresburgerCheck formula freeOf location -> do
        symbol <- internSymbol (PresburgerSymbol formula (Map.keys freeOf) location)
        meta <- sourceMetadata location
        headRoot <- internTerm [1, fromIntegral symbol, 0, 0, 0, fromIntegral meta]
        foldM (apply meta) headRoot (Map.elems freeOf)
    where
        apply meta function argument = do
            argument' <- compileTerm argument
            internTerm [2, fromIntegral function, fromIntegral argument', 0, 0, fromIntegral meta]

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
            index <- gets (IntMap.size . builtMetadata)
            modify (\state -> state { builtMetadata = IntMap.insert index meta (builtMetadata state), metadataKeys = Map.insert key index (metadataKeys state) })
            return index

internSymbol :: FullSymbol -> Compile Int
internSymbol symbol = do
    let key = symbolIdentity symbol
    known <- gets (Map.lookup key . symbolKeys)
    case known of
        Just index -> return index
        Nothing -> do
            index <- gets (IntMap.size . builtSymbols)
            modify (\state -> state { builtSymbols = IntMap.insert index symbol (builtSymbols state), symbolKeys = Map.insert key index (symbolKeys state) })
            return index

internTerm :: [Int64] -> Compile Int
internTerm words = do
    known <- gets (Map.lookup words . termKeys)
    case known of
        Just index -> return index
        Nothing -> do
            index <- gets (IntMap.size . builtTerms)
            modify (\state -> state { builtTerms = IntMap.insert index words (builtTerms state), termKeys = Map.insert words index (termKeys state) })
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
