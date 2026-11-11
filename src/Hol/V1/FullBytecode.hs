module Hol.V1.FullBytecode where

import qualified Calc.Presburger.Internal as P
import Control.Monad
import Data.Int
import qualified Data.IntMap.Strict as IntMap
import qualified Data.IntSet as IntSet
import qualified Data.List as List
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Hol.BETA.Constant
import Hol.BETA.Header
import Hol.BETA.TermNode
import Hol.V1.Bytecode (ArtifactNumber (..), readBounded, readConstructor)
import Text.Read (Read (..), ReadPrec, pfail, readListPrecDefault, readMaybe, step)
import Z.Utils (Unique (..))

data FullSymbol
    = ConstantSymbol Constant
    | PresburgerSymbol P.MyPresburgerFormulaRep [P.MyVar] (Maybe SLoc)
    deriving ()

data NodeMetadata
    = NodeMetadata
        { nodeHint :: Maybe String
        , nodeType :: LamType
        , nodeLocation :: Maybe SLoc
        }
    deriving ()

data FullProgram
    = FullProgram
        { fullWords :: [Int64]
        , fullSymbols :: IntMap.IntMap FullSymbol
        , fullVariables :: [LogicVar]
        , fullMetadata :: IntMap.IntMap NodeMetadata
        , fullKindEnv :: KindEnv
        , fullTypeEnv :: TypeEnv
        , fullQueryTypes :: Map.Map LogicVar (MonoType Int)
        }
    deriving ()

withRuntimeMetadata :: KindEnv -> TypeEnv -> Map.Map LogicVar (MonoType Int) -> FullProgram -> FullProgram
withRuntimeMetadata kinds types variables program = enriched { fullKindEnv = kinds, fullTypeEnv = types, fullQueryTypes = variables } where
    wanted = map (ConstantSymbol . TC) (Map.keys kinds) ++ map (ConstantSymbol . DC) (Map.keys types)
    existing = fullSymbols program
    identities = Set.fromList (map symbolIdentity (IntMap.elems existing))
    (symbols, _) = List.foldl' addSymbol (existing, identities) wanted
    addSymbol (current, seen) symbol
        | identity `Set.member` seen = (current, seen)
        | otherwise = (IntMap.insert (IntMap.size current) symbol current, Set.insert identity seen)
        where
            identity = symbolIdentity symbol
    enriched = case fullSections (fullWords program) of
        Right ([magic, version, terms, _, facts, slots, root, metadata], slotRows, _, termRows, factRows, payload) -> program
            { fullSymbols = symbols
            , fullWords = [magic, version, terms, fromIntegral (IntMap.size symbols), facts, slots, root, metadata] ++ concat slotRows ++ map (fromIntegral . symbolRole) (IntMap.elems symbols) ++ concat termRows ++ concat factRows ++ payload
            }
        _ -> program

-- The DTOs preserve identities and kinds; the surface pretty-printers are not
-- parsers for serialized runtime metadata.
data StoredCon
    = SCData String
    | SCType String
    | SCDataUnique Int (Maybe String)
    | SCTypeUnique Int
    | SCBuiltin Int
    | SCLogical Int
    | SCChar Char
    | SCNat Integer
    deriving (Eq, Ord, Show)

instance Read StoredCon where
    readPrec = readConstructor $ \constructor -> case constructor of
        "SCData" -> SCData <$> step readPrec
        "SCType" -> SCType <$> step readPrec
        "SCDataUnique" -> SCDataUnique <$> step readBounded <*> step readPrec
        "SCTypeUnique" -> SCTypeUnique <$> step readBounded
        "SCBuiltin" -> SCBuiltin <$> step readBounded
        "SCLogical" -> SCLogical <$> step readBounded
        "SCChar" -> SCChar <$> step readPrec
        "SCNat" -> SCNat <$> step readPrec
        _ -> pfail
    readListPrec = readListPrecDefault

data StoredKind
    = SKStar
    | SKArrow StoredKind StoredKind
    deriving (Eq, Ord, Read, Show)

data StoredType
    = STVar Int
    | STMeta Int
    | STCon StoredCon StoredKind
    | STApp StoredType StoredType
    deriving (Eq, Ord, Show)

instance Read StoredType where
    readPrec = readConstructor $ \constructor -> case constructor of
        "STVar" -> STVar <$> step readBounded
        "STMeta" -> STMeta <$> step readBounded
        "STCon" -> STCon <$> step readPrec <*> step readPrec
        "STApp" -> STApp <$> step readPrec <*> step readPrec
        _ -> pfail
    readListPrec = readListPrecDefault

data StoredVar
    = SVNamed String
    | SVGenerated Int (Maybe String)
    | SVType Int
    deriving (Eq, Ord, Show)

instance Read StoredVar where
    readPrec = readConstructor $ \constructor -> case constructor of
        "SVNamed" -> SVNamed <$> step readPrec
        "SVGenerated" -> SVGenerated <$> step readBounded <*> step readPrec
        "SVType" -> SVType <$> step readBounded
        _ -> pfail
    readListPrec = readListPrecDefault

data StoredFormula
    = SFTruth Bool
    | SFRelation Int StoredPterm StoredPterm
    | SFModulo StoredPterm Integer StoredPterm
    | SFNot StoredFormula
    | SFConnect Int StoredFormula StoredFormula
    | SFQuant Bool Integer StoredFormula
    deriving (Eq, Ord, Show)

instance Read StoredFormula where
    readPrec = readConstructor $ \constructor -> case constructor of
        "SFTruth" -> SFTruth <$> step readPrec
        "SFRelation" -> SFRelation <$> step readBounded <*> step readPrec <*> step readPrec
        "SFModulo" -> SFModulo <$> step readPrec <*> step readPrec <*> step readPrec
        "SFNot" -> SFNot <$> step readPrec
        "SFConnect" -> SFConnect <$> step readBounded <*> step readPrec <*> step readPrec
        "SFQuant" -> SFQuant <$> step readPrec <*> step readPrec <*> step readPrec
        _ -> pfail
    readListPrec = readListPrecDefault

data StoredPterm
    = SPVar Integer
    | SPZero
    | SPSucc StoredPterm
    | SPPlus StoredPterm StoredPterm
    deriving (Eq, Ord, Read, Show)

data StoredSymbol
    = SSConstant StoredCon
    | SSPresburger StoredFormula [Integer] (Maybe ((Int, Int), (Int, Int)))
    deriving (Show)

instance Read StoredSymbol where
    readPrec = readConstructor $ \constructor -> case constructor of
        "SSConstant" -> SSConstant <$> step readPrec
        "SSPresburger" -> SSPresburger <$> step readPrec <*> step readPrec <*> step readArtifactLocation
        _ -> pfail
    readListPrec = readListPrecDefault

type ArtifactLocation = Maybe ((ArtifactNumber Int, ArtifactNumber Int), (ArtifactNumber Int, ArtifactNumber Int))

artifactLocation :: ArtifactLocation -> Maybe ((Int, Int), (Int, Int))
artifactLocation = fmap (\((line1, column1), (line2, column2)) -> ((unArtifactNumber line1, unArtifactNumber column1), (unArtifactNumber line2, unArtifactNumber column2)))

readArtifactLocation :: ReadPrec (Maybe ((Int, Int), (Int, Int)))
readArtifactLocation = artifactLocation <$> readPrec

data FullArtifact
    = FullArtifact Int [Int64] [StoredSymbol] [StoredVar] [(Maybe String, Maybe StoredType, Maybe ((Int, Int), (Int, Int)))] [(StoredCon, StoredKind)] [(StoredCon, [String], StoredType)] [(StoredVar, StoredType)]
    deriving (Show)

instance Read FullArtifact where
    readPrec = readConstructor $ \constructor -> do
        guard (constructor == "FullArtifact")
        version <- step readBounded
        words <- map unArtifactNumber <$> step readPrec
        symbols <- step readPrec
        variables <- step readPrec
        metadata <- step readPrec
        kinds <- step readPrec
        types <- step readPrec
        queryTypes <- step readPrec
        return (FullArtifact version words symbols variables [(hint, typ, artifactLocation location) | (hint, typ, location) <- metadata] kinds types queryTypes)
    readListPrec = readListPrecDefault

logicalOperators :: [LogicalOperator]
logicalOperators = [LO_ty_pi, LO_if, LO_true, LO_fail, LO_cut, LO_and, LO_or, LO_imply, LO_pi, LO_sigma, LO_debug, LO_is]

builtinConstants :: [Constant]
builtinConstants = map DC [DC_Nil, DC_Cons, DC_Succ, DC_eq, DC_le, DC_lt, DC_ge, DC_gt, DC_plus, DC_minus, DC_mul, DC_div, DC_wc] ++ [TC TC_Arrow]

storeCon :: Constant -> StoredCon
storeCon constant = case constant of
    DC (DC_Named name) -> SCData name
    TC (TC_Named name) -> SCType name
    DC (DC_Unique (Unique key) (DispHint hint)) -> SCDataUnique key hint
    TC (TC_Unique (Unique key)) -> SCTypeUnique key
    DC (DC_ChrL ch) -> SCChar ch
    DC (DC_NatL value) -> SCNat value
    DC (DC_LO operator) -> SCLogical (indexOf operator logicalOperators)
    _ -> SCBuiltin (indexOf constant builtinConstants)
    where
        indexOf value = length . takeWhile (/= value)

restoreCon :: StoredCon -> Either String Constant
restoreCon stored = case stored of
    SCData name -> Right (DC (DC_Named name))
    SCType name -> Right (TC (TC_Named name))
    SCDataUnique key hint -> nonnegative key >> Right (DC (DC_Unique (Unique key) (DispHint hint)))
    SCTypeUnique key -> nonnegative key >> Right (TC (TC_Unique (Unique key)))
    SCChar ch -> Right (DC (DC_ChrL ch))
    SCNat value -> unless (value >= 0) (Left "negative natural constant") >> Right (DC (DC_NatL value))
    SCLogical index -> DC . DC_LO <$> checkedIndex logicalOperators index
    SCBuiltin index -> checkedIndex builtinConstants index
    where
        nonnegative value = unless (value >= 0) (Left "negative constant identifier")

checkedIndex :: [a] -> Int -> Either String a
checkedIndex values index
    | index < 0 = Left "negative metadata index"
    | otherwise = case drop index values of
        value : _ -> Right value
        [] -> Left "unknown metadata index"

storeKind :: KindExpr -> StoredKind
storeKind Star = SKStar
storeKind (KArr lhs rhs) = SKArrow (storeKind lhs) (storeKind rhs)

restoreKind :: StoredKind -> KindExpr
restoreKind SKStar = Star
restoreKind (SKArrow lhs rhs) = KArr (restoreKind lhs) (restoreKind rhs)

storeType :: MonoType Int -> StoredType
storeType typ = case typ of
    TyVar index -> STVar index
    TyMTV (Unique key) -> STMeta key
    TyCon (TCon con kind) -> STCon (storeCon (TC con)) (storeKind kind)
    TyApp lhs rhs -> STApp (storeType lhs) (storeType rhs)

restoreType :: StoredType -> Either String (MonoType Int)
restoreType typ = case typ of
    STVar index -> nonnegative index >> Right (TyVar index)
    STMeta key -> Right (TyMTV (Unique key))
    STCon con kind -> do
        decoded <- restoreCon con
        case decoded of
            TC constructor -> Right (TyCon (TCon constructor (restoreKind kind)))
            _ -> Left "data constructor used as a type constructor"
    STApp lhs rhs -> TyApp <$> restoreType lhs <*> restoreType rhs
    where
        nonnegative value = unless (value >= 0) (Left "negative type identifier")

storeVar :: LogicVar -> StoredVar
storeVar variable = case variable of
    LV_Named name -> SVNamed name
    LV_Unique (Unique key) (DispHint hint) -> SVGenerated key hint
    LV_ty_var (Unique key) -> SVType key

restoreVar :: StoredVar -> Either String LogicVar
restoreVar variable = case variable of
    SVNamed name -> Right (LV_Named name)
    SVGenerated key hint -> nonnegative key >> Right (LV_Unique (Unique key) (DispHint hint))
    SVType key -> nonnegative key >> Right (LV_ty_var (Unique key))
    where
        nonnegative value = unless (value >= 0) (Left "negative variable identifier")

storeLocation :: SLoc -> ((Int, Int), (Int, Int))
storeLocation (SLoc begin end) = (begin, end)

restoreLocation :: ((Int, Int), (Int, Int)) -> Either String SLoc
restoreLocation (begin@(line1, column1), end@(line2, column2)) = do
    unless (all (>= 1) [line1, column1, line2, column2] && begin <= end) (Left "invalid source coordinate")
    return (SLoc begin end)

storeFormula :: P.MyPresburgerFormulaRep -> StoredFormula
storeFormula formula = case formula of
    P.ValF value -> SFTruth value
    P.EqnF lhs rhs -> SFRelation 0 (storePterm lhs) (storePterm rhs)
    P.LtnF lhs rhs -> SFRelation 1 (storePterm lhs) (storePterm rhs)
    P.LeqF lhs rhs -> SFRelation 2 (storePterm lhs) (storePterm rhs)
    P.GtnF lhs rhs -> SFRelation 3 (storePterm lhs) (storePterm rhs)
    P.ModF lhs modulus rhs -> SFModulo (storePterm lhs) modulus (storePterm rhs)
    P.NegF body -> SFNot (storeFormula body)
    P.DisF lhs rhs -> SFConnect 0 (storeFormula lhs) (storeFormula rhs)
    P.ConF lhs rhs -> SFConnect 1 (storeFormula lhs) (storeFormula rhs)
    P.ImpF lhs rhs -> SFConnect 2 (storeFormula lhs) (storeFormula rhs)
    P.IffF lhs rhs -> SFConnect 3 (storeFormula lhs) (storeFormula rhs)
    P.AllF variable body -> SFQuant True variable (storeFormula body)
    P.ExsF variable body -> SFQuant False variable (storeFormula body)

storePterm :: P.PresburgerTermRep -> StoredPterm
storePterm term = case term of
    P.IVar variable -> SPVar variable
    P.Zero -> SPZero
    P.Succ body -> SPSucc (storePterm body)
    P.Plus lhs rhs -> SPPlus (storePterm lhs) (storePterm rhs)

restoreFormula :: StoredFormula -> Either String P.MyPresburgerFormulaRep
restoreFormula formula = case formula of
    SFTruth value -> Right (P.ValF value)
    SFRelation tag lhs rhs -> do
        constructor <- checkedIndex [P.EqnF, P.LtnF, P.LeqF, P.GtnF] tag
        constructor <$> restorePterm lhs <*> restorePterm rhs
    SFModulo lhs modulus rhs -> do
        unless (modulus > 0) (Left "nonpositive Presburger modulus")
        lhs' <- restorePterm lhs
        rhs' <- restorePterm rhs
        return (P.ModF lhs' modulus rhs')
    SFNot body -> P.NegF <$> restoreFormula body
    SFConnect tag lhs rhs -> do
        constructor <- checkedIndex [P.DisF, P.ConF, P.ImpF, P.IffF] tag
        constructor <$> restoreFormula lhs <*> restoreFormula rhs
    SFQuant universal variable body -> do
        unless (variable > 0) (Left "nonpositive Presburger variable")
        (if universal then P.AllF variable else P.ExsF variable) <$> restoreFormula body

restorePterm :: StoredPterm -> Either String P.PresburgerTermRep
restorePterm term = case term of
    SPVar variable -> unless (variable > 0) (Left "nonpositive Presburger variable") >> Right (P.IVar variable)
    SPZero -> Right P.Zero
    SPSucc body -> P.Succ <$> restorePterm body
    SPPlus lhs rhs -> P.Plus <$> restorePterm lhs <*> restorePterm rhs

storeSymbol :: FullSymbol -> StoredSymbol
storeSymbol symbol = case symbol of
    ConstantSymbol constant -> SSConstant (storeCon constant)
    PresburgerSymbol formula variables location -> SSPresburger (storeFormula formula) variables (fmap storeLocation location)

symbolIdentity :: FullSymbol -> String
symbolIdentity symbol = show $ case storeSymbol symbol of
    SSConstant (SCDataUnique key _) -> SSConstant (SCDataUnique key Nothing)
    SSPresburger formula variables _ -> SSPresburger formula variables Nothing
    stored -> stored

restoreSymbol :: StoredSymbol -> Either String FullSymbol
restoreSymbol symbol = case symbol of
    SSConstant constant -> ConstantSymbol <$> restoreCon constant
    SSPresburger formula variables location -> do
        unless (all (> 0) variables && Set.size (Set.fromList variables) == length variables) (Left "invalid Presburger free-variable table")
        decoded <- restoreFormula formula
        unless (P.getFVs decoded `Set.isSubsetOf` Set.fromList variables) (Left "missing Presburger free-variable binding")
        PresburgerSymbol decoded variables <$> traverse restoreLocation location

storeMetadata :: NodeMetadata -> (Maybe String, Maybe StoredType, Maybe ((Int, Int), (Int, Int)))
storeMetadata (NodeMetadata hint (LamType typ) location) = (hint, fmap storeType typ, fmap storeLocation location)

restoreMetadata :: (Maybe String, Maybe StoredType, Maybe ((Int, Int), (Int, Int))) -> Either String NodeMetadata
restoreMetadata (hint, typ, location) = NodeMetadata hint <$> (LamType <$> traverse restoreType typ) <*> traverse restoreLocation location

serializeFullBytecode :: FullProgram -> Either String String
serializeFullBytecode program = do
    validateFullBytecode program
    return $ show (FullArtifact 2 (fullWords program) symbols variables metadata kinds types queryTypes) ++ "\n"
    where
        symbols = map storeSymbol (IntMap.elems (fullSymbols program))
        variables = map storeVar (fullVariables program)
        metadata = map storeMetadata (IntMap.elems (fullMetadata program))
        kinds = [(storeCon (TC con), storeKind kind) | (con, kind) <- Map.toList (fullKindEnv program)]
        types = [(storeCon (DC con), names, storeType typ) | (con, Forall names typ) <- Map.toList (fullTypeEnv program)]
        queryTypes = [(storeVar variable, storeType typ) | (variable, typ) <- Map.toList (fullQueryTypes program)]

deserializeFullBytecode :: String -> Either String FullProgram
deserializeFullBytecode text = case readMaybe text of
    Nothing -> Left "invalid full HOL V1 bytecode artifact"
    Just (FullArtifact version words symbols variables metadata kinds types queryTypes) -> do
        unless (version == 2) (Left "unsupported full HOL V1 artifact version")
        symbols' <- mapM restoreSymbol symbols
        variables' <- mapM restoreVar variables
        metadata' <- mapM restoreMetadata metadata
        kinds' <- mapM restoreKindEntry kinds
        types' <- mapM restoreTypeEntry types
        queryTypes' <- mapM (\(variable, typ) -> (,) <$> restoreVar variable <*> restoreType typ) queryTypes
        unless (distinctKeys kinds' && distinctKeys types' && distinctKeys queryTypes') (Left "duplicate type metadata key")
        let program = FullProgram words (IntMap.fromList (zip [0 ..] symbols')) variables' (IntMap.fromList (zip [0 ..] metadata')) (Map.fromList kinds') (Map.fromList types') (Map.fromList queryTypes')
        validateFullBytecode program
        return program
    where
        distinctKeys entries = Set.size (Set.fromList (map fst entries)) == length entries
        restoreKindEntry (stored, kind) = do
            constant <- restoreCon stored
            case constant of
                TC con -> Right (con, restoreKind kind)
                _ -> Left "invalid kind environment constructor"
        restoreTypeEntry (stored, names, typ) = do
            constant <- restoreCon stored
            decoded <- restoreType typ
            case constant of
                DC con -> Right (con, Forall names decoded)
                _ -> Left "invalid type environment constructor"

symbolRole :: FullSymbol -> Int
symbolRole (PresburgerSymbol _ _ _) = 20
symbolRole (ConstantSymbol constant) = case constant of
    DC (DC_LO operator) -> 1 + length (takeWhile (/= operator) logicalOperators)
    DC DC_eq -> 13
    DC DC_le -> 14
    DC DC_lt -> 15
    DC DC_ge -> 16
    DC DC_gt -> 17
    DC (DC_Named "read") -> 18
    DC (DC_Named "print") -> 19
    DC DC_Succ -> 21
    DC (DC_Named "flex") -> 22
    DC DC_plus -> 23
    DC DC_minus -> 23
    DC DC_mul -> 23
    DC DC_div -> 23
    TC (TC_Named "nat") -> 24
    _ -> 0

fullSections :: [Int64] -> Either String ([Int64], [[Int64]], [Int64], [[Int64]], [[Int64]], [Int64])
fullSections words = case take 8 words of
    [magic, version, _, _, _, _, entry, _]
        | magic == 0x484f4c31 && version == 2 && entry < 0 -> Left "negative full bytecode count"
    _ -> fragmentSections 0 words

-- A fragment is loaded on a machine that has `known` symbols already: its
-- symbol count is the total after it, and its symbol section has the roles of
-- the new ones. Its templates, clauses and digits are numbered from zero. A
-- fragment that only extends the program has no query slot and the entry -1.
fragmentSections :: Int -> [Int64] -> Either String ([Int64], [[Int64]], [Int64], [[Int64]], [[Int64]], [Int64])
fragmentSections known words = case splitAt 8 words of
    (header@[magic, version, terms, symbols, facts, slots, entry, metadata], rest) -> do
        unless (magic == 0x484f4c31 && version == 2) (Left "unsupported full bytecode magic or version")
        unless (all (>= 0) [terms, symbols, facts, slots, metadata] && entry >= -1) (Left "negative full bytecode count")
        unless (toInteger known <= toInteger symbols) (Left "a full bytecode fragment has fewer symbols than its program")
        unless (entry >= 0 || slots == 0) (Left "a full bytecode fragment has query slots and no query")
        let fixed = 2 * toInteger slots + (toInteger symbols - toInteger known) + 6 * toInteger terms + 2 * toInteger facts
        unless (fixed <= toInteger (length rest)) (Left "truncated full bytecode sections")
        unless (entry < terms) (Left "invalid full bytecode query entry")
        let (slotWords, afterSlots) = splitAt (2 * fromIntegral slots) rest
            (roleWords, afterRoles) = splitAt (fromIntegral symbols - known) afterSlots
            (termWords, afterTerms) = splitAt (6 * fromIntegral terms) afterRoles
            (factWords, payload) = splitAt (2 * fromIntegral facts) afterTerms
        return (header, chunks 2 slotWords, roleWords, chunks 6 termWords, chunks 2 factWords, payload)
    _ -> Left "truncated full bytecode header"
    where
        chunks _ [] = []
        chunks count values = take count values : chunks count (drop count values)

validateFullBytecode :: FullProgram -> Either String ()
validateFullBytecode program = fullSections (fullWords program) >>= validateSections (const False) 0 0 program

-- The tables of `program` are those of the program its fragment is loaded on,
-- with what the fragment adds. The first `knownSymbols` symbols, which have the
-- identities `known`, and the first `knownMetadata` annotations were validated
-- with an earlier fragment: only the additions are examined.
validateFullFragment :: (String -> Bool) -> Int -> Int -> FullProgram -> Either String ()
validateFullFragment known knownSymbols knownMetadata program = fragmentSections knownSymbols (fullWords program) >>= validateSections known knownSymbols knownMetadata program

validateSections :: (String -> Bool) -> Int -> Int -> FullProgram -> ([Int64], [[Int64]], [Int64], [[Int64]], [[Int64]], [Int64]) -> Either String ()
validateSections known knownSymbols knownMetadata program (header, slots, roles, terms, facts, payload) = do
    let (_, newSymbols) = IntMap.split (knownSymbols - 1) (fullSymbols program)
        (_, newMetadata) = IntMap.split (knownMetadata - 1) (fullMetadata program)
        identities = map symbolIdentity (IntMap.elems newSymbols)
    case header of
        [_, _, termCount, symbolCount, _, slotCount, entry, metadataCount] -> do
            unless (IntMap.keys newSymbols == [knownSymbols .. fromIntegral symbolCount - 1]) (Left "full symbol metadata count mismatch")
            unless (Set.size (Set.fromList identities) == length identities && not (any known identities)) (Left "duplicate full symbol identity")
            unless (IntMap.keys newMetadata == [knownMetadata .. fromIntegral metadataCount - 1]) (Left "full annotation metadata count mismatch")
            unless (toInteger (length (fullVariables program)) == toInteger slotCount) (Left "full query variable count mismatch")
            unless (Set.size (Set.fromList (fullVariables program)) == length (fullVariables program)) (Left "duplicate full query variable")
            unless (roles == map (fromIntegral . symbolRole) (IntMap.elems newSymbols)) (Left "symbol roles do not match metadata")
            unless (all (\digit -> digit >= 48 && digit <= 57) payload) (Left "invalid natural literal payload")
            mapM_ (restoreSymbol . storeSymbol) (IntMap.elems newSymbols)
            mapM_ (restoreMetadata . storeMetadata) (IntMap.elems newMetadata)
            mapM_ (restoreVar . storeVar) (fullVariables program)
            mapM_ (checkSlot metadataCount) (zip slots (fullVariables program))
            mapM_ (checkTerm termCount symbolCount slotCount metadataCount (length payload, IntSet.fromDistinctAscList [offset | (offset, 48) <- zip [0 ..] payload])) (zip [0 ..] terms)
            mapM_ (checkFact termCount symbolCount) facts
            let depths = foldl depthOf IntMap.empty (zip [0 ..] terms)
            unless (entry == -1 || IntMap.lookup (fromIntegral entry) depths == Just 0) (Left "unbound de Bruijn index in full query")
            forM_ facts $ \row -> case row of
                [_, root] -> unless (IntMap.lookup (fromIntegral root) depths == Just 0) (Left "unbound de Bruijn index in full clause")
                _ -> Left "invalid full clause"
        _ -> Left "invalid full bytecode header"
    where
        checkIndex count index = unless (index >= 0 && index < count) (Left "invalid full bytecode reference")
        checkMeta count index = unless (index == -1 || (index >= 0 && index < count)) (Left "invalid annotation reference")
        checkSlot count ([isType, meta], variable) = do
            unless (isType == if isTypeVariable variable then 1 else 0) (Left "query type-variable metadata mismatch")
            checkMeta count meta
        checkSlot _ _ = Left "invalid query slot"
        isTypeVariable (LV_ty_var _) = True
        isTypeVariable _ = False
        checkTerm _ symbols slots metadata (digitCount, zeroDigits) (index, [tag, a, b, c, d, meta]) = do
            checkMeta metadata meta
            unless (c == 0 && d == 0) (Left "invalid reserved template operand")
            case tag of
                0 -> checkIndex slots a >> zero b
                1 -> checkIndex symbols a >> zero b
                2 -> checkIndex index a >> checkIndex index b
                3 -> unless (a >= 0) (Left "negative de Bruijn index") >> zero b
                4 -> checkIndex index a >> zero b
                5 -> do
                    unless (a >= 0 && b > 0 && toInteger a + toInteger b <= toInteger digitCount) (Left "invalid natural payload reference")
                    unless (b == 1 || IntSet.notMember (fromIntegral a) zeroDigits) (Left "noncanonical natural literal")
                6 -> zero a >> zero b
                _ -> Left "unknown full bytecode term tag"
        checkTerm _ _ _ _ _ _ = Left "invalid full bytecode term"
        checkFact terms symbols [predicate, root] = do
            unless (predicate == -1 || (predicate >= 0 && predicate < symbols)) (Left "invalid clause predicate reference")
            checkIndex terms root
        checkFact _ _ _ = Left "invalid full bytecode clause"
        zero operand = unless (operand == 0) (Left "invalid reserved template operand")
        depthOf table (index, row) = IntMap.insert index required table where
            required = case row of
                [3, deBruijn, _, _, _, _] -> toInteger deBruijn + 1
                [2, left, right, _, _, _] -> max (child left) (child right)
                [4, body, _, _, _, _] -> max 0 (child body - 1)
                _ -> 0
            child root = IntMap.findWithDefault 0 (fromIntegral root) table

disassembleFull :: FullProgram -> String
disassembleFull program = case fullSections (fullWords program) of
    Left reason -> "Invalid full HOL V1 bytecode: " ++ reason ++ "\n"
    Right (header, slots, roles, terms, facts, _) -> unlines $ concat
        [ ["HOL V1 bytecode version 2", "HEADER " ++ show header]
        , ["SLOT " ++ show index ++ " " ++ show slot | (index, slot) <- zip [0 :: Int ..] slots]
        , ["SYMBOL " ++ show index ++ " role=" ++ show role ++ " " ++ show (storeSymbol symbol) | ((index, symbol), role) <- zip (IntMap.toAscList (fullSymbols program)) roles]
        , ["TERM " ++ show index ++ " " ++ render row | (index, row) <- zip [0 :: Int ..] terms]
        , ["CLAUSE " ++ show index ++ " " ++ show row | (index, row) <- zip [0 :: Int ..] facts]
        , ["EXEC " ++ show (header !! 6)]
        ]
    where
        render [tag, a, b, _, _, meta] = case tag of
            0 -> "VAR " ++ show a
            1 -> "CONST " ++ show a
            2 -> "APP " ++ show a ++ " " ++ show b
            3 -> "INDEX " ++ show a
            4 -> "LAM " ++ show a ++ " metadata=" ++ show meta
            5 -> "NAT offset=" ++ show a ++ " length=" ++ show b
            6 -> "WILDCARD"
            _ -> "UNKNOWN " ++ show tag
        render row = show row

fullUniqueFloor :: FullProgram -> Either String Int
fullUniqueFloor program
    | largest == maxBound = Left "full bytecode has exhausted variable identifiers"
    | otherwise = Right (largest + 1)
    where
        largest = maximum (0 : keys)
        keys = concatMap varKeys (fullVariables program)
            ++ concatMap symbolKeys (IntMap.elems (fullSymbols program))
            ++ concatMap (maybe [] typeKeys . unLamType . nodeType) (IntMap.elems (fullMetadata program))
            ++ concatMap (typeKeys . snd) (Map.toList (fullQueryTypes program))
            ++ concatMap (\(Forall _ typ) -> typeKeys typ) (Map.elems (fullTypeEnv program))
        varKeys (LV_Named _) = []
        varKeys (LV_Unique (Unique key) _) = [key]
        varKeys (LV_ty_var (Unique key)) = [key]
        symbolKeys (ConstantSymbol constant) = conKeys constant
        symbolKeys _ = []
        conKeys (DC (DC_Unique (Unique key) _)) = [key]
        conKeys (TC (TC_Unique (Unique key))) = [key]
        conKeys _ = []
        typeKeys (TyMTV (Unique key)) = [key]
        typeKeys (TyCon (TCon con _)) = conKeys (TC con)
        typeKeys (TyApp lhs rhs) = typeKeys lhs ++ typeKeys rhs
        typeKeys _ = []

data TemplateValue
    = TemplateTerm TermNode
    | TemplateFormula P.MyPresburgerFormulaRep [P.MyVar] [TermNode] (Maybe SLoc)
    deriving ()

-- Reconstruct compiled terms for diagnostics and answer projection only.
-- Execution always uses the native graph and never this presentation view.
fullSourceTerms :: FullProgram -> Either String ([TermNode], TermNode)
fullSourceTerms program = do
    validateFullBytecode program
    (clauses, goal) <- fragmentSourceTerms 0 program
    maybe (Left "missing full query") (\query -> return (clauses, query)) goal

-- The clauses and the query of a validated fragment that is loaded on a program
-- with `known` symbols. A fragment that only extends the program has no query.
fragmentSourceTerms :: Int -> FullProgram -> Either String ([TermNode], Maybe TermNode)
fragmentSourceTerms known program = do
    (header, _, _, rows, facts, payload) <- fragmentSections known (fullWords program)
    table <- foldM (decodeTemplate payload) IntMap.empty (zip [0 ..] rows)
    clauses <- mapM (fact table) facts
    goal <- if header !! 6 < 0 then return Nothing else Just <$> (lookupTerm table (header !! 6) >>= finish)
    return (clauses, goal)
    where
        fact table [_, root] = lookupTerm table root >>= finish
        fact _ _ = Left "invalid full clause record"
        lookupTerm table root = maybe (Left "missing full template") Right (IntMap.lookup (fromIntegral root) table)
        finish (TemplateTerm term) = Right term
        finish _ = Left "incomplete Presburger term in bytecode"
        decodeTemplate payload table (index, [tag, a, b, _, _, meta]) = do
            let info = IntMap.findWithDefault (NodeMetadata Nothing noLamType Nothing) (fromIntegral meta) (fullMetadata program)
                location = nodeLocation info
                child root = lookupTerm table root >>= finish
            result <- case tag of
                0 -> TemplateTerm . mkLVar <$> checkedIndex (fullVariables program) (fromIntegral a)
                1 -> case IntMap.lookup (fromIntegral a) (fullSymbols program) of
                    Just (ConstantSymbol constant) -> Right (TemplateTerm (mkNConLoc location constant))
                    Just (PresburgerSymbol formula [] source) -> Right (TemplateTerm (NPresburgerCheck formula Map.empty source))
                    Just (PresburgerSymbol formula variables source) -> Right (TemplateFormula formula variables [] source)
                    Nothing -> Left "unknown full bytecode constant"
                2 -> do
                    function <- lookupTerm table a
                    argument <- child b
                    case function of
                        TemplateTerm term -> Right (TemplateTerm (mkNAppLoc location term argument))
                        TemplateFormula formula variables arguments source
                            | length arguments + 1 == length variables -> Right (TemplateTerm (NPresburgerCheck formula (Map.fromList (zip variables (arguments ++ [argument]))) source))
                            | otherwise -> Right (TemplateFormula formula variables (arguments ++ [argument]) source)
                3 -> Right (TemplateTerm (mkNIdx (fromIntegral a)))
                4 -> TemplateTerm . (\body -> NLam (nodeHint info) (nodeType info) body location) <$> child a
                5 -> do
                    let digits = take (fromIntegral b) (drop (fromIntegral a) payload)
                        value = foldl (\number digit -> number * 10 + toInteger (digit - 48)) 0 digits
                    Right (TemplateTerm (mkNConLoc location (DC_NatL value)))
                6 -> Right (TemplateTerm (mkNConLoc location DC_wc))
                _ -> Left "unknown full template tag"
            return (IntMap.insert index result table)
        decodeTemplate _ _ _ = Left "invalid full template record"

queryFromBytecode :: FullProgram -> Either String TermNode
queryFromBytecode = fmap snd . fullSourceTerms
