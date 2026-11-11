module Hol.V1.Compiler (compileProgram) where

import Control.Monad
import Control.Monad.Trans.Class
import Control.Monad.Trans.State.Strict
import Data.Int
import qualified Data.IntMap.Strict as IntMap
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Hol.BETA.Constant
import Hol.BETA.Header
import Hol.BETA.HOPU (getLVars)
import Hol.BETA.Runtime (expandAssumptions)
import Hol.BETA.TermNode
import Hol.V1.Bytecode

data Template
    = Variable Int
    | Constant Int
    | Application Int Int
    deriving (Eq, Ord)

data Instruction
    = Return
    | Fail
    | Call Int Int
    | Unify Int Int Int
    | Choice Int Int
    | Cut Int
    deriving ()

data ClauseSource
    = ClauseSource
        { sourcePredicate :: Constant
        , sourceBinders :: Int
        , sourceHead :: TermNode
        , sourceBody :: TermNode
        , sourceHasSuccessor :: Bool
        }
    deriving ()

data Build
    = Build
        { terms :: IntMap.IntMap Template
        , termIndices :: Map.Map Template Int
        , instructions :: IntMap.IntMap Instruction
        , symbols :: Map.Map Constant Int
        , constants :: IntMap.IntMap Constant
        , clauses :: [[Int64]]
        , predicateArities :: Map.Map Constant Int
        , needed :: Set.Set Constant
        , compiled :: Set.Set Constant
        }
    deriving ()

data Locals
    = Locals
        { binderSlots :: [Int]
        , variableSlots :: Map.Map LogicVar Int
        , nextSlot :: Int
        , knownConstants :: Map.Map Int Constant
        }
    deriving ()

data GoalCode
    = Succeed
    | Failure
    | Invoke Int
    | Match Int Int
    | Commit
    | Sequence GoalCode GoalCode
    | Alternative GoalCode GoalCode
    deriving ()

type Compile = StateT Build (Either String)

type CompileLocal = StateT Locals Compile

compileProgram :: [TermNode] -> TermNode -> Either String CompiledProgram
compileProgram facts query = assertNonnegativeTerms facts `seq` assertNonnegativeIndices query `seq` do
    when (containsSuccessor query) (Left "Hol V1: successor terms require the general V1 runtime")
    sources <- concat <$> mapM expandFact facts
    let vars = Set.toAscList (getLVars query)
        queryLocals = Locals [] (Map.fromList (zip vars [0 ..])) (length vars) Map.empty
        initial = Build IntMap.empty Map.empty (IntMap.fromList [(0, Return), (1, Fail)]) Map.empty IntMap.empty [] Map.empty Set.empty Set.empty
    when (any isTypeVariable vars) (Left "Hol V1: a query with unresolved type variables requires the general V1 runtime")
    ((entry, slots), result) <- runStateT (buildProgram sources queryLocals) initial
    let header = [bytecodeMagic, bytecodeVersion, fromIntegral (IntMap.size (terms result)), fromIntegral (IntMap.size (instructions result)), fromIntegral (length (clauses result)), fromIntegral slots, fromIntegral entry, fromIntegral (IntMap.size (constants result))]
        words = header ++ concatMap encodeTerm (IntMap.elems (terms result)) ++ concatMap encodeInstruction (IntMap.elems (instructions result)) ++ concat (reverse (clauses result))
    let program = CompiledProgram
            { bytecodeWords = words
            , bytecodeConstants = constants result
            , bytecodeVariables = vars
            , bytecodeQuerySlots = slots
            }
    validateBytecode program
    return program
    where
        isTypeVariable (LV_ty_var _) = True
        isTypeVariable _ = False
        expandFact fact = mapM (inspectClause (containsSuccessor fact)) (expandAssumptions fact)
        buildProgram sources queryLocals = do
            (entry, locals) <- runStateT (compileGoal sources query 0) queryLocals
            compileReachable sources
            return (entry, nextSlot locals)

unsupported :: String -> Compile a
unsupported message = lift (Left ("Hol V1: " ++ message))

unsupportedLocal :: String -> CompileLocal a
unsupportedLocal = lift . unsupported

inspectClause :: Bool -> TermNode -> Either String ClauseSource
inspectClause hasSuccessor = strip 0 where
    strip count fact = case unfoldlNApp (rewrite HNF fact) of
        (NCon (DC (DC_LO operator)) _, [NLam _ _ body _])
            | operator == LO_ty_pi || operator == LO_pi -> strip (count + 1) body
        (NCon (DC (DC_LO LO_if)) _, [headTerm, body]) -> finish count headTerm body
        _ -> finish count fact (mkNCon LO_true)
    finish count headTerm body = case unfoldlNApp (rewrite HNF headTerm) of
        (NCon predicate _, _) -> Right (ClauseSource predicate count headTerm body hasSuccessor)
        _ -> Left "Hol V1: a program clause has a nonconstant predicate"

compileReachable :: [ClauseSource] -> Compile ()
compileReachable sources = do
    state <- get
    case Set.lookupMin (needed state `Set.difference` compiled state) of
        Nothing -> return ()
        Just predicate -> do
            modify (\s -> s { compiled = Set.insert predicate (compiled s) })
            mapM_ (compileClause sources) [ source | source <- sources, sourcePredicate source == predicate ]
            compileReachable sources

compileClause :: [ClauseSource] -> ClauseSource -> Compile ()
compileClause sources source = do
    when (sourceHasSuccessor source) (unsupported "successor terms require the general V1 runtime")
    registerArity (sourcePredicate source) (length (snd (unfoldlNApp (sourceHead source))))
    symbol <- internSymbol (sourcePredicate source)
    ((headRoot, entry), locals) <- runStateT compile (Locals (reverse [0 .. count - 1]) Map.empty count Map.empty)
    modify (\s -> s { clauses = [fromIntegral symbol, fromIntegral (nextSlot locals), fromIntegral headRoot, fromIntegral entry] : clauses s })
    where
        count = sourceBinders source
        compile = do
            headRoot <- compileTerm (sourceHead source)
            entry <- compileGoal sources (sourceBody source) 0
            return (headRoot, entry)

compileGoal :: [ClauseSource] -> TermNode -> Int -> CompileLocal Int
compileGoal sources goal next = do
    code <- lowerGoal sources goal
    lift (emitGoal code next)

-- Analyze bindings in execution order before constructing continuations.
lowerGoal :: [ClauseSource] -> TermNode -> CompileLocal GoalCode
lowerGoal sources goal = case unfoldlNApp goal of
    (NCon (DC (DC_LO LO_true)) _, []) -> return Succeed
    (NCon (DC (DC_LO LO_fail)) _, []) -> return Failure
    (NCon (DC (DC_LO LO_cut)) _, []) -> return Commit
    (NCon (DC (DC_LO LO_and)) _, [left, right]) -> do
        first <- lowerGoal sources left
        second <- lowerGoal sources right
        return (Sequence first second)
    (NCon (DC (DC_LO LO_or)) _, [left, right]) -> do
        incoming <- gets knownConstants
        first <- lowerGoal sources left
        leftKnown <- gets knownConstants
        modify (\s -> s { knownConstants = incoming })
        second <- lowerGoal sources right
        rightKnown <- gets knownConstants
        let agreed = Map.mergeWithKey (\_ lhs rhs -> if lhs == rhs then Just lhs else Nothing) (const Map.empty) (const Map.empty) leftKnown rightKnown
        modify (\s -> s { knownConstants = agreed })
        return (Alternative first second)
    (NCon (DC (DC_LO LO_sigma)) _, [NLam _ _ body _]) -> do
        outer <- gets binderSlots
        slot <- gets nextSlot
        modify (\s -> s { binderSlots = slot : outer, nextSlot = slot + 1 })
        code <- lowerGoal sources body
        modify (\s -> s { binderSlots = outer, knownConstants = Map.delete slot (knownConstants s) })
        return code
    (NCon (DC (DC_LO _)) _, _) -> unsupportedLocal "this logical operator requires the general V1 runtime"
    (NCon (DC DC_eq) _, [typ, left, right]) -> do
        leftSlot <- termSlot left
        rightSlot <- termSlot right
        leftKnown <- knownConstant left
        rightKnown <- knownConstant right
        let closedAlias = (isSlot leftSlot && isKnown rightKnown) || (isSlot rightSlot && isKnown leftKnown)
        unless (knownNonNatType typ || (arrowType typ && closedAlias)) (unsupportedLocal "natural or polymorphic equality requires the general V1 runtime")
        unless (standardEquality sources) (unsupportedLocal "custom equality clauses require the general V1 runtime")
        lhs <- compileTerm left
        rhs <- compileTerm right
        forM_ [(leftSlot, rightKnown), (rightSlot, leftKnown)] $ \pair -> case pair of
            (Just slot, Just constant) -> modify (\s -> s { knownConstants = Map.insert slot constant (knownConstants s) })
            _ -> return ()
        return (Match lhs rhs)
    (headTerm, args) -> do
        resolved <- knownConstant headTerm
        case resolved of
            Just predicate
                | callable predicate -> do
                    root <- compileTerm (foldlNApp (mkNCon predicate) args)
                    lift $ do
                        registerArity predicate (length args)
                        modify (\s -> s { needed = Set.insert predicate (needed s) })
                    return (Invoke root)
            _ -> unsupportedLocal "higher-order or dynamic goals require the general V1 runtime"
    where
        isSlot (Just _) = True
        isSlot Nothing = False
        isKnown (Just _) = True
        isKnown Nothing = False

termSlot :: TermNode -> CompileLocal (Maybe Int)
termSlot term = case term of
    LVar variable -> gets (Map.lookup variable . variableSlots)
    NIdx index -> do
        slots <- gets binderSlots
        return $ if index < 0 then Nothing else case drop index slots of
            slot : _ -> Just slot
            [] -> Nothing
    _ -> return Nothing

knownConstant :: TermNode -> CompileLocal (Maybe Constant)
knownConstant (NCon constant _)
    | callable constant = return (Just constant)
knownConstant term = do
    slot <- termSlot term
    known <- gets knownConstants
    return (slot >>= (`Map.lookup` known))

arrowType :: TermNode -> Bool
arrowType typ = case unfoldlNApp typ of
    (NCon (TC TC_Arrow) _, [_, _]) -> True
    _ -> False

emitGoal :: GoalCode -> Int -> Compile Int
emitGoal code next = case code of
    Succeed -> return next
    Failure -> return 1
    Invoke root -> emit (Call root next)
    Match left right -> emit (Unify left right next)
    Commit -> emit (Cut next)
    Sequence first second -> do
        rest <- emitGoal second next
        emitGoal first rest
    Alternative first second -> do
        left <- emitGoal first next
        right <- emitGoal second next
        emit (Choice left right)

callable :: Constant -> Bool
callable (DC (DC_Named name)) = name /= "read" && name /= "print" && name /= "flex"
callable _ = False

knownNonNatType :: TermNode -> Bool
knownNonNatType typ = case unfoldlNApp typ of
    (NCon (TC (TC_Named name)) _, _) -> name /= "nat"
    _ -> False

standardEquality :: [ClauseSource] -> Bool
standardEquality sources = case [ source | source <- sources, sourcePredicate source == DC DC_eq ] of
    [source] -> case (unfoldlNApp (sourceHead source), unfoldlNApp (sourceBody source)) of
        ((NCon (DC DC_eq) _, [NIdx ty, NIdx lhs, NIdx rhs]), (NCon (DC (DC_LO LO_true)) _, [])) -> ty /= lhs && lhs == rhs && sourceBinders source == 2
        _ -> False
    _ -> False

compileTerm :: TermNode -> CompileLocal Int
compileTerm term = case term of
    LVar variable -> do
        locals <- get
        case Map.lookup variable (variableSlots locals) of
            Just slot -> lift (internTerm (Variable slot))
            Nothing -> unsupportedLocal "a program clause contains an unclosed logic variable"
    NIdx index -> do
        slot <- termSlot term
        case slot of
            Just value -> lift (internTerm (Variable value))
            Nothing -> unsupportedLocal "an unbound de Bruijn index requires the general V1 runtime"
    NCon (DC DC_wc) _ -> do
        slot <- gets nextSlot
        modify (\s -> s { nextSlot = slot + 1 })
        lift (internTerm (Variable slot))
    NCon constant _ -> do
        unless (plainConstant constant) (unsupportedLocal "this constant requires the general V1 runtime")
        lift (internSymbol constant >>= internTerm . Constant)
    NApp left right _ -> do
        case fst (unfoldlNApp term) of
            NCon (DC DC_wc) _ -> unsupportedLocal "an applied wildcard requires the general V1 runtime"
            NCon _ _ -> return ()
            _ -> unsupportedLocal "a flexible application requires the general V1 runtime"
        lhs <- compileTerm left
        rhs <- compileTerm right
        lift (internTerm (Application lhs rhs))
    _ -> unsupportedLocal "lambda terms, suspensions, and Presburger goals require the general V1 runtime"

plainConstant :: Constant -> Bool
plainConstant (DC (DC_Named name)) = name /= "read" && name /= "print" && name /= "flex"
plainConstant (DC DC_Nil) = True
plainConstant (DC DC_Cons) = True
plainConstant (DC (DC_ChrL _)) = True
plainConstant (DC (DC_NatL value)) = value >= 0
plainConstant (TC TC_Arrow) = True
plainConstant (TC (TC_Named _)) = True
plainConstant _ = False

containsSuccessor :: TermNode -> Bool
containsSuccessor term = case term of
    NCon (DC DC_Succ) _ -> True
    NApp left right _ -> containsSuccessor left || containsSuccessor right
    NLam _ _ body _ -> containsSuccessor body
    Susp body _ _ env -> containsSuccessor body || any itemContainsSuccessor env
    NPresburgerCheck _ freeOf _ -> any containsSuccessor (Map.elems freeOf)
    _ -> False
    where
        itemContainsSuccessor (Dummy _) = False
        itemContainsSuccessor (Binds body _) = containsSuccessor body

registerArity :: Constant -> Int -> Compile ()
registerArity predicate arity = do
    known <- gets (Map.lookup predicate . predicateArities)
    case known of
        Just previous
            | previous /= arity -> unsupported "inconsistent predicate arity requires the general V1 runtime"
        _ -> modify (\s -> s { predicateArities = Map.insert predicate arity (predicateArities s) })

internSymbol :: Constant -> Compile Int
internSymbol constant = do
    state <- get
    case Map.lookup constant (symbols state) of
        Just index -> return index
        Nothing -> do
            let index = Map.size (symbols state)
            put state { symbols = Map.insert constant index (symbols state), constants = IntMap.insert index constant (constants state) }
            return index

internTerm :: Template -> Compile Int
internTerm term = do
    state <- get
    case Map.lookup term (termIndices state) of
        Just index -> return index
        Nothing -> do
            let index = Map.size (termIndices state)
            put state { terms = IntMap.insert index term (terms state), termIndices = Map.insert term index (termIndices state) }
            return index

emit :: Instruction -> Compile Int
emit instruction = do
    index <- gets (maybe 0 ((+ 1) . fst) . IntMap.lookupMax . instructions)
    modify (\s -> s { instructions = IntMap.insert index instruction (instructions s) })
    return index

encodeTerm :: Template -> [Int64]
encodeTerm (Variable slot) = [0, fromIntegral slot, 0]
encodeTerm (Constant symbol) = [1, fromIntegral symbol, 0]
encodeTerm (Application left right) = [2, fromIntegral left, fromIntegral right]

encodeInstruction :: Instruction -> [Int64]
encodeInstruction Return = [0, 0, 0, 0]
encodeInstruction Fail = [1, 0, 0, 0]
encodeInstruction (Call term next) = [2, fromIntegral term, fromIntegral next, 0]
encodeInstruction (Unify left right next) = [3, fromIntegral left, fromIntegral right, fromIntegral next]
encodeInstruction (Choice left right) = [4, fromIntegral left, fromIntegral right, 0]
encodeInstruction (Cut next) = [5, fromIntegral next, 0, 0]
