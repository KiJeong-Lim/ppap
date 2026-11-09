module Hol.V1.Bytecode where

import Control.Monad
import Data.Int
import qualified Data.IntMap.Strict as IntMap
import qualified Data.List as List
import qualified Data.Set as Set
import Hol.BETA.Constant
import Hol.BETA.Header
import Hol.BETA.TermNode (LogicVar (..))
import Text.Read (Lexeme (Ident), Read (..), lexP, parens, pfail, prec, readListPrecDefault, readMaybe, step)
import Z.Utils (Unique (..))

data CompiledProgram
    = CompiledProgram
        { bytecodeWords :: [Int64]
        , bytecodeConstants :: IntMap.IntMap Constant
        , bytecodeVariables :: [LogicVar]
        , bytecodeQuerySlots :: Int
        }
    deriving ()

bytecodeMagic :: Int64
bytecodeMagic = 0x484f4c31

bytecodeVersion :: Int64
bytecodeVersion = 1

disassemble :: CompiledProgram -> String
disassemble program = case sections (bytecodeWords program) of
    Left err -> "Invalid HOL V1 bytecode: " ++ err ++ "\n"
    Right (header, termRows, instructionRows, clauseRows) -> unlines $ concat
        [ [ "HOL V1 bytecode version " ++ show bytecodeVersion
            , "HEADER " ++ show header
            ]
        , [ "SYMBOL " ++ show index ++ " " ++ show constant | (index, constant) <- IntMap.toAscList (bytecodeConstants program) ]
        , [ "TERM " ++ show index ++ " " ++ renderTerm row | (index, row) <- zip [0 :: Int ..] termRows ]
        , [ "CODE " ++ show index ++ " " ++ renderInstruction row | (index, row) <- zip [0 :: Int ..] instructionRows ]
        , [ "CLAUSE " ++ show index ++ " " ++ show row | (index, row) <- zip [0 :: Int ..] clauseRows ]
        ]
    where
        renderTerm [0, slot, _] = "VAR " ++ show slot
        renderTerm [1, symbol, _] = "CONST " ++ show symbol
        renderTerm [2, left, right] = "APP " ++ show left ++ " " ++ show right
        renderTerm row = show row
        renderInstruction [0, _, _, _] = "RETURN"
        renderInstruction [1, _, _, _] = "FAIL"
        renderInstruction [2, term, next, _] = "CALL " ++ show term ++ " -> " ++ show next
        renderInstruction [3, left, right, next] = "UNIFY " ++ show left ++ " " ++ show right ++ " -> " ++ show next
        renderInstruction [4, left, right, _] = "CHOICE " ++ show left ++ " " ++ show right
        renderInstruction [5, next, _, _] = "CUT -> " ++ show next
        renderInstruction row = show row

data StoredConstant
    = DataName String
    | Nil
    | Cons
    | Character Char
    | Natural Integer
    | TypeArrow
    | TypeName String
    deriving (Read, Show)

data StoredVariable
    = TypeVariable Int
    | NamedVariable String
    | GeneratedVariable Int (Maybe String)
    deriving (Read, Show)

data BytecodeArtifact
    = BytecodeArtifact Int64 [Int64] [(Int, StoredConstant)] [StoredVariable] Int
    deriving (Show)

instance Read BytecodeArtifact where
    readPrec = parens $ prec 10 $ do
        Ident constructor <- lexP
        guard (constructor == "BytecodeArtifact")
        version <- step readPrec >>= bounded
        words <- step readPrec >>= mapM bounded
        constants <- step readPrec
        variables <- step readPrec
        slots <- step readPrec
        return (BytecodeArtifact version words constants variables slots)
        where
            bounded value
                | value >= toInteger (minBound :: Int64) && value <= toInteger (maxBound :: Int64) = return (fromInteger value)
                | otherwise = pfail
    readListPrec = readListPrecDefault

readBytecodeArtifact :: String -> Maybe BytecodeArtifact
readBytecodeArtifact text = canonical `mplus` readMaybe text where
    canonical = do
        table <- List.stripPrefix "BytecodeArtifact 1 [" text
        (words, rest) <- decimalWords table
        BytecodeArtifact version _ constants variables slots <- readMaybe ("BytecodeArtifact 1 []" ++ rest)
        return (BytecodeArtifact version words constants variables slots)

-- The emitted word table is decimal; the bounded Read fallback preserves
-- other accepted notation without allowing Int64 wraparound.
decimalWords :: String -> Maybe ([Int64], String)
decimalWords (']' : rest) = Just ([], rest)
decimalWords input = do
    (value, rest) <- decimalWord input
    collect [value] rest
    where
        collect values (']' : rest) = Just (reverse values, rest)
        collect values (',' : rest) = do
            (value, remaining) <- decimalWord rest
            collect (value : values) remaining
        collect _ _ = Nothing

decimalWord :: String -> Maybe (Int64, String)
decimalWord ('-' : rest) = digits True rest
decimalWord input = digits False input

digits :: Bool -> String -> Maybe (Int64, String)
digits negative input = case input of
    ch : _
        | decimal ch -> scan 0 input
    _ -> Nothing
    where
        limit = if negative then minBound else negate (maxBound :: Int64)
        threshold = limit `quot` 10
        finalDigit = negate (limit `rem` 10)
        decimal ch = ch >= '0' && ch <= '9'
        scan value (ch : rest)
            | decimal ch = do
                let digit = fromIntegral (fromEnum ch - fromEnum '0')
                guard (value > threshold || (value == threshold && digit <= finalDigit))
                let next = value * 10 - digit
                next `seq` scan next rest
        scan value rest = Just (if negative then value else negate value, rest)

serializeBytecode :: CompiledProgram -> Either String String
serializeBytecode program = do
    validateBytecode program
    storedConstants <- mapM storeConstant (IntMap.toAscList (bytecodeConstants program))
    return (show (BytecodeArtifact bytecodeVersion (bytecodeWords program) storedConstants (map storeVariable (bytecodeVariables program)) (bytecodeQuerySlots program)) ++ "\n")
    where
        storeConstant (index, constant) = (,) index <$> case constant of
            DC (DC_Named name) -> Right (DataName name)
            DC DC_Nil -> Right Nil
            DC DC_Cons -> Right Cons
            DC (DC_ChrL ch) -> Right (Character ch)
            DC (DC_NatL n)
                | n >= 0 -> Right (Natural n)
            TC TC_Arrow -> Right TypeArrow
            TC (TC_Named name) -> Right (TypeName name)
            _ -> Left "a constant cannot be represented in the V1 artifact"
        storeVariable (LV_ty_var (Unique key)) = TypeVariable key
        storeVariable (LV_Named name) = NamedVariable name
        storeVariable (LV_Unique (Unique key) (DispHint hint)) = GeneratedVariable key hint

deserializeBytecode :: String -> Either String CompiledProgram
deserializeBytecode text = case readBytecodeArtifact text of
    Nothing -> Left "invalid HOL V1 bytecode artifact"
    Just (BytecodeArtifact version words storedConstants storedVariables slots) -> do
        unless (version == bytecodeVersion) (Left "unsupported HOL V1 artifact version")
        unless (map fst storedConstants == [0 .. length storedConstants - 1]) (Left "noncontiguous HOL V1 symbol table")
        decodedConstants <- mapM restoreConstant storedConstants
        let program = CompiledProgram words (IntMap.fromList decodedConstants) (map restoreVariable storedVariables) slots
        validateBytecode program
        return program
    where
        restoreConstant (index, constant) = (,) index <$> case constant of
            DataName name -> Right (DC (DC_Named name))
            Nil -> Right (DC DC_Nil)
            Cons -> Right (DC DC_Cons)
            Character ch -> Right (DC (DC_ChrL ch))
            Natural n
                | n >= 0 -> Right (DC (DC_NatL n))
                | otherwise -> Left "negative natural in HOL V1 artifact"
            TypeArrow -> Right (TC TC_Arrow)
            TypeName name -> Right (TC (TC_Named name))
        restoreVariable (TypeVariable key) = LV_ty_var (Unique key)
        restoreVariable (NamedVariable name) = LV_Named name
        restoreVariable (GeneratedVariable key hint) = LV_Unique (Unique key) (DispHint hint)

sections :: [Int64] -> Either String ([Int64], [[Int64]], [[Int64]], [[Int64]])
sections words = case splitAt 8 words of
    (header@[magic, version, termCount, instructionCount, clauseCount, slots, entry, symbolCount], rest) -> do
        unless (magic == bytecodeMagic && version == bytecodeVersion) (Left "unsupported bytecode magic or version")
        unless (all (>= 0) [termCount, instructionCount, clauseCount, slots, entry, symbolCount]) (Left "negative bytecode header field")
        let expected = 3 * toInteger termCount + 4 * toInteger instructionCount + 4 * toInteger clauseCount
        unless (toInteger (length rest) == expected) (Left "bytecode section length mismatch")
        let (termWords, afterTerms) = splitAt (3 * fromIntegral termCount) rest
            (instructionWords, clauseWords) = splitAt (4 * fromIntegral instructionCount) afterTerms
        return (header, chunks 3 termWords, chunks 4 instructionWords, chunks 4 clauseWords)
    _ -> Left "truncated bytecode header"
    where
        chunks _ [] = []
        chunks size values = take size values : chunks size (drop size values)

validateBytecode :: CompiledProgram -> Either String ()
validateBytecode program = do
    (header, termRows, instructionRows, clauseRows) <- sections (bytecodeWords program)
    case header of
        [_, _, termCount, instructionCount, _, slots, entry, symbolCount] -> do
            unless (slots == fromIntegral (bytecodeQuerySlots program) && length (bytecodeVariables program) <= bytecodeQuerySlots program) (Left "query slot metadata mismatch")
            unless (IntMap.keys (bytecodeConstants program) == [0 .. fromIntegral symbolCount - 1]) (Left "symbol table metadata mismatch")
            unless (Set.size (Set.fromList (IntMap.elems (bytecodeConstants program))) == IntMap.size (bytecodeConstants program)) (Left "duplicate constant in symbol table")
            unless (Set.size (Set.fromList (bytecodeVariables program)) == length (bytecodeVariables program)) (Left "duplicate query variable")
            mapM_ checkConstant (IntMap.elems (bytecodeConstants program))
            mapM_ checkVariable (bytecodeVariables program)
            checkIndex "query entry" instructionCount entry
            mapM_ (checkTerm symbolCount) (zip [0 ..] termRows)
            mapM_ (checkInstruction termCount instructionCount) instructionRows
            mapM_ (checkClause symbolCount termCount instructionCount) clauseRows
            let termInfo = List.foldl' summarizeTerm IntMap.empty (zip [0 ..] termRows)
                code = IntMap.fromList (zip [0 ..] instructionRows)
            checkContext termInfo code slots entry
            mapM_ (checkClauseContext termInfo code) clauseRows
        _ -> Left "invalid bytecode header"
    where
        checkConstant constant = case constant of
            DC (DC_Named _) -> Right ()
            DC DC_Nil -> Right ()
            DC DC_Cons -> Right ()
            DC (DC_ChrL _) -> Right ()
            DC (DC_NatL n) -> unless (n >= 0) (Left "negative natural constant")
            TC TC_Arrow -> Right ()
            TC (TC_Named _) -> Right ()
            _ -> Left "constant outside the first-order bytecode domain"
        checkVariable variable = case variable of
            LV_Named _ -> Right ()
            LV_Unique (Unique key) _ -> unless (key >= 0) (Left "negative query variable identifier")
            LV_ty_var (Unique key)
                | key < 0 -> Left "negative query type variable identifier"
                | otherwise -> Left "unresolved query type variable"
        checkIndex what count index = unless (index >= 0 && index < count) (Left ("invalid " ++ what ++ " reference"))
        checkTerm symbolCount (index, row) = case row of
            [0, slot, 0] -> unless (slot >= 0) (Left "negative variable slot")
            [1, symbol, 0] -> checkIndex "constant" symbolCount symbol
            [2, left, right] -> checkIndex "term child" index left >> checkIndex "term child" index right
            _ -> Left "invalid term template"
        checkInstruction termCount instructionCount row = case row of
            [0, 0, 0, 0] -> Right ()
            [1, 0, 0, 0] -> Right ()
            [2, term, next, 0] -> checkIndex "call term" termCount term >> checkIndex "continuation" instructionCount next
            [3, left, right, next] -> checkIndex "unification term" termCount left >> checkIndex "unification term" termCount right >> checkIndex "continuation" instructionCount next
            [4, left, right, 0] -> checkIndex "choice" instructionCount left >> checkIndex "choice" instructionCount right
            [5, next, 0, 0] -> checkIndex "cut continuation" instructionCount next
            _ -> Left "invalid bytecode instruction"
        checkClause symbolCount termCount instructionCount row = case row of
            [symbol, slots, headTerm, entry] -> do
                checkIndex "clause predicate" symbolCount symbol
                unless (slots >= 0) (Left "negative clause slot count")
                checkIndex "clause head" termCount headTerm
                checkIndex "clause entry" instructionCount entry
            _ -> Left "invalid bytecode clause"
        summarizeTerm table (index, row) = IntMap.insert index info table where
            info = case row of
                [0, slot, 0] -> (toInteger slot + 1, Nothing)
                [1, symbol, 0] -> (0, Just symbol)
                [2, left, right] ->
                    let (leftSlots, symbol) = table IntMap.! fromIntegral left
                        (rightSlots, _) = table IntMap.! fromIntegral right
                    in (max leftSlots rightSlots, symbol)
                _ -> (0, Nothing)
        checkClauseContext termInfo code [symbol, slots, headTerm, entry] = do
            let (requiredSlots, headSymbol) = termInfo IntMap.! fromIntegral headTerm
            unless (headSymbol == Just symbol) (Left "clause head does not match its predicate")
            unless (requiredSlots <= toInteger slots) (Left "clause head refers outside its variable environment")
            checkContext termInfo code slots entry
        checkClauseContext _ _ _ = Left "invalid bytecode clause"
        checkContext termInfo code slots entry = visit Set.empty [entry] where
            checkRoot root = unless (fst (termInfo IntMap.! fromIntegral root) <= toInteger slots) (Left "instruction refers outside its variable environment")
            visit _ [] = Right ()
            visit seen (pc : rest)
                | Set.member pc seen = visit seen rest
                | otherwise = do
                    let seen' = Set.insert pc seen
                    case code IntMap.! fromIntegral pc of
                        [2, root, next, 0] -> checkRoot root >> visit seen' (next : rest)
                        [3, left, right, next] -> checkRoot left >> checkRoot right >> visit seen' (next : rest)
                        [4, left, right, 0] -> visit seen' (left : right : rest)
                        [5, next, 0, 0] -> visit seen' (next : rest)
                        _ -> visit seen' rest
