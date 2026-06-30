module Hol.BETA.Arith
    ( ParseResult (..)
    , LiftResult (..)
    , parsePresburger
    , zonkPresburger
    , liftConstraint
    , renumberFormula
    , entails
    , arithEntails
    , ArithStore
    , presburgerStoreSat
    , presburgerEntails
    , presburgerValid
    , installPresburger
    , installPresburgerWithEnv
    ) where

import Calc.Presburger.Internal
import Control.Monad.Trans.State.Strict (State, get, put, runState)
import Data.Char (isAlphaNum, isDigit, isSpace)
import qualified Data.List as List
import qualified Data.Map.Strict as Map
import Data.Maybe (mapMaybe)
import qualified Data.Set as Set
import Hol.BETA.Constant
import Hol.BETA.Diagnostic
import Hol.BETA.Header
import Hol.BETA.TermNode
import qualified Z.Doc
import Z.Utils (ErrMsg, unUnique)

data ParseResult
    = ParseResult
        { _formula :: MyPresburgerFormulaRep
        , _freeOfFormula :: Map.Map MyVar TermNode
        , _updatedEnv :: Map.Map LargeId TermNode
        }
    deriving ()

data LiftResult
    = LiftResult
        { _liftedFormula :: MyPresburgerFormulaRep
        , _freeOfLifted :: Map.Map MyVar TermNode
        }
    deriving ()

parsePresburger :: SLoc -> String -> Map.Map LargeId TermNode -> Either ErrMsg ParseResult
parsePresburger sloc src env0
    = case runP parseTop initState of
        Left msg -> Left (locPrefix ++ msg)
        Right (f, st') -> Right (ParseResult { _formula = f, _freeOfFormula = psFreeMap st', _updatedEnv = psNameToVar st' })
    where
        locPrefix = "presburger[" ++ shows (_BegPos sloc) "]: "
        initState = PState
            { psInput = src
            , psNameToVar = env0
            , psBoundStack = []
            , psFreeMap = Map.empty
            , psInverseFree = Map.empty
            , psNextVar = theMinNumOfMyVar
            }
        parseTop = do
            f <- parseFormula
            skipWS
            leftover <- getInput
            if null leftover then return f else throwP ("unexpected trailing input: " ++ shows (take 20 leftover) "")

data PState
    = PState
        { psInput :: !String
        , psNameToVar :: !(Map.Map LargeId TermNode)
        , psBoundStack :: ![(LargeId, MyVar)]
        , psFreeMap :: !(Map.Map MyVar TermNode)
        , psInverseFree :: !(Map.Map TermNode MyVar)
        , psNextVar :: !MyVar
        }
    deriving ()

newtype P a
    = P { runP :: PState -> Either ErrMsg (a, PState) }
    deriving ()

instance Functor P where
    fmap f (P g) = P $ \s -> case g s of
        Left e -> Left e
        Right (a, s') -> Right (f a, s')

instance Applicative P where
    pure x = P $ \s -> Right (x, s)
    P f <*> P g = P $ \s -> case f s of
        Left e -> Left e
        Right (h, s') -> case g s' of
            Left e -> Left e
            Right (x, s'') -> Right (h x, s'')

instance Monad P where
    P g >>= k = P $ \s -> case g s of
        Left e -> Left e
        Right (a, s') -> runP (k a) s'

throwP :: ErrMsg -> P a
throwP msg = P $ \_ -> Left msg

getInput :: P String
getInput = P $ \s -> Right (psInput s, s)

setInput :: String -> P ()
setInput inp = P $ \s -> Right ((), s { psInput = inp })

getState :: P PState
getState = P $ \s -> Right (s, s)

setState :: PState -> P ()
setState s' = P $ \_ -> Right ((), s')

modify :: (PState -> PState) -> P ()
modify f = P $ \s -> Right ((), f s)

tryP :: P a -> P (Maybe a)
tryP (P g) = P $ \s -> case g s of
    Left _ -> Right (Nothing, s)
    Right (a, s') -> Right (Just a, s')

skipWS :: P ()
skipWS = do
    inp <- getInput
    setInput (dropWhile isSpace inp)

literal :: String -> P Bool
literal lit = do
    skipWS
    inp <- getInput
    case List.stripPrefix lit inp of
        Just rest -> do { setInput rest; return True }
        Nothing -> return False

mustLiteral :: String -> P ()
mustLiteral lit = do
    ok <- literal lit
    if ok then
        return ()
    else do
        inp <- getInput
        throwP ("expected " ++ shows lit (", got: " ++ shows (take 20 inp) ""))

isIdentStart :: Char -> Bool
isIdentStart c = (c >= 'A' && c <= 'Z') || c == '_'

isIdentCont :: Char -> Bool
isIdentCont c = isAlphaNum c || c == '_'

upperIdent :: P (Maybe LargeId)
upperIdent = do
    skipWS
    inp <- getInput
    case inp of
        (c : cs)
            | isIdentStart c -> do
                let (rest, more) = span isIdentCont cs
                setInput more
                return (Just (c : rest))
        _ -> return Nothing

mustUpperIdent :: P LargeId
mustUpperIdent = do
    m <- upperIdent
    case m of
        Just s -> return s
        Nothing -> throwP "expected an uppercase identifier"

decimalNat :: P (Maybe Integer)
decimalNat = do
    skipWS
    inp <- getInput
    let (digs, rest) = span isDigit inp
    if null digs then
        return Nothing
    else do
        setInput rest
        return (Just (read digs))

natToTermRep :: Integer -> PresburgerTermRep
natToTermRep n
    | n <= 0 = Zero
    | otherwise = Succ (natToTermRep (n - 1))

resolveVar :: LargeId -> P MyVar
resolveVar name
    = do
        st <- getState
        case lookup name (psBoundStack st) of
            Just v -> return v
            Nothing -> case Map.lookup name (psNameToVar st) of
                Just t -> reuseOrAlloc t
                Nothing -> do
                    let t = mkLVar (LV_Named name)
                    modify $ \s -> s { psNameToVar = Map.insert name t (psNameToVar s) }
                    reuseOrAlloc t
    where
        reuseOrAlloc t = do
            st <- getState
            case Map.lookup t (psInverseFree st) of
                Just v -> return v
                Nothing -> do
                    let v = psNextVar st
                    modify $ \s -> s { psFreeMap = Map.insert v t (psFreeMap s) , psInverseFree = Map.insert t v (psInverseFree s) , psNextVar = v + 1 }
                    return v

freshBoundVar :: P MyVar
freshBoundVar = do
    st <- getState
    let v = psNextVar st
    modify $ \s -> s { psNextVar = v + 1 }
    return v

withBound :: LargeId -> MyVar -> P a -> P a
withBound name v action = do
    modify $ \s -> s { psBoundStack = (name, v) : psBoundStack s }
    r <- action
    modify $ \s -> s { psBoundStack = drop 1 (psBoundStack s) }
    return r

parseArith :: P PresburgerTermRep
parseArith
    = do
        t1 <- parseArithAtom
        parseArithRest t1
    where
        parseArithRest acc = do
            skipWS
            inp <- getInput
            case inp of
                ('+' : rest) -> do
                    setInput rest
                    t2 <- parseArithAtom
                    parseArithRest (Plus acc t2)
                _ -> return acc

parseArithAtom :: P PresburgerTermRep
parseArithAtom = do
    skipWS
    inp <- getInput
    case inp of
        '(' : _ -> do
            mustLiteral "("
            t <- parseArith
            mustLiteral ")"
            return t
        c : _
            | isDigit c -> do
                mn <- decimalNat
                case mn of
                    Just n -> return (natToTermRep n)
                    Nothing -> throwP "expected decimal literal"
        c : _
            | isIdentStart c -> do
                name <- mustUpperIdent
                v <- resolveVar name
                return (IVar v)
        _ -> throwP ("expected arithmetic atom, got: " ++ shows (take 20 inp) "")

parseFormula :: P MyPresburgerFormulaRep
parseFormula = parseLevel0

parseLevel0 :: P MyPresburgerFormulaRep
parseLevel0 = do
    f1 <- parseLevel1
    skipWS
    inp <- getInput
    case inp of
        '<' : '-' : '>' : rest -> do
            setInput rest
            f2 <- parseLevel0
            return (IffF f1 f2)
        '-' : '>' : rest -> do
            setInput rest
            f2 <- parseLevel0
            return (ImpF f1 f2)
        _ -> return f1

parseLevel1 :: P MyPresburgerFormulaRep
parseLevel1
    = do
        f1 <- parseLevel2
        rest f1
    where
        rest acc = do
            skipWS
            inp <- getInput
            case inp of
                '\\' : '/' : more -> do
                    setInput more
                    f2 <- parseLevel2
                    rest (DisF acc f2)
                _ -> return acc

parseLevel2 :: P MyPresburgerFormulaRep
parseLevel2
    = do
        f1 <- parseLevel3
        rest f1
    where
        rest acc = do
            skipWS
            inp <- getInput
            case inp of
                '/' : '\\' : more -> do
                    setInput more
                    f2 <- parseLevel3
                    rest (ConF acc f2)
                _ -> return acc

parseLevel3 :: P MyPresburgerFormulaRep
parseLevel3
    = do
        skipWS
        inp <- getInput
        case inp of
            '~' : rest -> do
                setInput rest
                f <- parseLevel3
                return (NegF f)
            _
                | keywordAt "forall" inp -> do
                    setInput (drop 6 inp)
                    parseQuantifierBody AllF
            _
                | keywordAt "exists" inp -> do
                    setInput (drop 6 inp)
                    parseQuantifierBody ExsF
            _ -> parseLevel4
    where
        keywordAt kw s = and
            [ kw `List.isPrefixOf` s
            , case drop (length kw) s of
                [] -> True
                (c : _) -> not (isIdentCont c)
            ]

parseQuantifierBody :: (MyVar -> MyPresburgerFormulaRep -> MyPresburgerFormulaRep) -> P MyPresburgerFormulaRep
parseQuantifierBody ctor = do
    name <- mustUpperIdent
    mustLiteral ","
    v <- freshBoundVar
    body <- withBound name v parseLevel3
    return (ctor v body)

parseLevel4 :: P MyPresburgerFormulaRep
parseLevel4 = do
    skipWS
    inp <- getInput
    case inp of
        '_' : '|' : '_' : rest -> do
            setInput rest
            return (ValF False)
        '(' : _ -> do
            mResult <- tryP $ do
                mustLiteral "("
                f <- parseFormula
                mustLiteral ")"
                return f
            case mResult of
                Just f -> return f
                Nothing -> parseAtomFormula
        _ -> parseAtomFormula

parseAtomFormula :: P MyPresburgerFormulaRep
parseAtomFormula = do
    t1 <- parseArith
    skipWS
    inp <- getInput
    case inp of
        '=' : '<' : rest -> do
            setInput rest
            t2 <- parseArith
            return (LeqF t1 t2)
        '=' : '=' : '_' : '{' : rest -> do
            setInput rest
            mn <- decimalNat
            mustLiteral "}"
            t2 <- parseArith
            case mn of
                Just n
                    | n > 0 -> return (ModF t1 (fromInteger n) t2)
                _ -> throwP "modulus must be a positive decimal literal"
        '=' : rest -> do
            setInput rest
            t2 <- parseArith
            return (EqnF t1 t2)
        '<' : rest -> do
            setInput rest
            t2 <- parseArith
            return (LtnF t1 t2)
        '>' : '=' : rest -> do
            setInput rest
            t2 <- parseArith
            return (NegF (LtnF t1 t2))
        '>' : rest -> do
            setInput rest
            t2 <- parseArith
            return (GtnF t1 t2)
        _ -> throwP ("expected a relational operator, got: " ++ shows (take 20 inp) "")

zonkPresburger :: Map.Map MyVar TermNode -> MyPresburgerFormulaRep -> MyPresburgerFormulaRep
zonkPresburger freeOf = goFormula Set.empty where
    goFormula bound (ValF b) = ValF b
    goFormula bound (EqnF t1 t2) = EqnF (goTerm bound t1) (goTerm bound t2)
    goFormula bound (LtnF t1 t2) = LtnF (goTerm bound t1) (goTerm bound t2)
    goFormula bound (LeqF t1 t2) = LeqF (goTerm bound t1) (goTerm bound t2)
    goFormula bound (GtnF t1 t2) = GtnF (goTerm bound t1) (goTerm bound t2)
    goFormula bound (ModF t1 r t2) = ModF (goTerm bound t1) r (goTerm bound t2)
    goFormula bound (NegF f1) = NegF (goFormula bound f1)
    goFormula bound (DisF f1 f2) = DisF (goFormula bound f1) (goFormula bound f2)
    goFormula bound (ConF f1 f2) = ConF (goFormula bound f1) (goFormula bound f2)
    goFormula bound (ImpF f1 f2) = ImpF (goFormula bound f1) (goFormula bound f2)
    goFormula bound (IffF f1 f2) = IffF (goFormula bound f1) (goFormula bound f2)
    goFormula bound (AllF y f1) = AllF y (goFormula (Set.insert y bound) f1)
    goFormula bound (ExsF y f1) = ExsF y (goFormula (Set.insert y bound) f1)

    goTerm bound (IVar v)
        | v `Set.member` bound
        = IVar v
        | otherwise
        = case Map.lookup v freeOf of
            Just t -> case asClosedNatLit (rewrite NF t) of
                Just n -> natToTermRep n
                Nothing -> IVar v
            Nothing -> IVar v
    goTerm _ Zero
        = Zero
    goTerm bound (Succ t)
        = Succ (goTerm bound t)
    goTerm bound (Plus t1 t2)
        = Plus (goTerm bound t1) (goTerm bound t2)

    asClosedNatLit :: TermNode -> Maybe Integer
    asClosedNatLit (NCon (DC (DC_NatL n)) _) = Just n
    asClosedNatLit _ = Nothing

liftConstraint :: TermNode -> Maybe LiftResult
liftConstraint t
    = case runLift (liftFormula t) emptyLS of
        Nothing -> Nothing
        Just (f, st) -> Just (LiftResult { _liftedFormula = f, _freeOfLifted = lsFreeMap st })
    where
        emptyLS = LiftState
            { lsFreeMap = Map.empty
            , lsInverse = Map.empty
            , lsNextVar = theMinNumOfMyVar
            }

data LiftState
    = LiftState
        { lsFreeMap :: !(Map.Map MyVar TermNode)
        , lsInverse :: !(Map.Map TermNode MyVar)
        , lsNextVar :: !MyVar
        }
    deriving ()

newtype L a
    = L { runLift :: LiftState -> Maybe (a, LiftState) }
    deriving ()

instance Functor L where
    fmap f (L g) = L $ \s -> case g s of
        Nothing -> Nothing
        Just (a, s') -> Just (f a, s')

instance Applicative L where
    pure x = L $ \s -> Just (x, s)
    L f <*> L g = L $ \s -> case f s of
        Nothing -> Nothing
        Just (h, s') -> case g s' of
            Nothing -> Nothing
            Just (x, s'') -> Just (h x, s'')

instance Monad L where
    L g >>= k = L $ \s -> case g s of
        Nothing -> Nothing
        Just (a, s') -> runLift (k a) s'

fail_ :: L a
fail_ = L $ \_ -> Nothing

allocL :: LogicVar -> L MyVar
allocL lv
    = L $ \s -> case Map.lookup (mkLVar lv) (lsInverse s) of
        Just v -> Just (v, s)
        Nothing -> let v = lsNextVar s
                       t = mkLVar lv
                   in Just (v, s { lsFreeMap = Map.insert v t (lsFreeMap s), lsInverse = Map.insert t v (lsInverse s), lsNextVar = v + 1 })

liftFormula :: TermNode -> L MyPresburgerFormulaRep
liftFormula t
    = case t of
        NApp (NApp (NApp (NCon (DC DC_eq) _) (NCon (TC (TC_Named "nat")) _) _) a _) b _ -> do 
            a' <- liftTerm a
            b' <- liftTerm b
            return (EqnF a' b')
        NApp (NApp (NCon (DC DC_lt) _) a _) b _ -> do
            a' <- liftTerm a
            b' <- liftTerm b
            return (LtnF a' b')
        NApp (NApp (NCon (DC DC_le) _) a _) b _ -> do
            a' <- liftTerm a
            b' <- liftTerm b
            return (LeqF a' b')
        NApp (NApp (NCon (DC DC_gt) _) a _) b _ -> do
            a' <- liftTerm a
            b' <- liftTerm b
            return (GtnF a' b')
        NApp (NApp (NCon (DC DC_ge) _) a _) b _ -> do
            a' <- liftTerm a
            b' <- liftTerm b
            return (NegF (LtnF a' b'))
        _ -> fail_

liftTerm :: TermNode -> L PresburgerTermRep
liftTerm t
    = case t of
        NCon (DC (DC_NatL n)) _
            | n >= 0 -> return (natToTermRep n)
            | otherwise -> fail_
        NApp (NCon (DC DC_Succ) _) a _ -> do
            a' <- liftTerm a
            return (Succ a')
        NApp (NApp (NCon (DC DC_plus) _) a _) b _ -> do
            a' <- liftTerm a
            b' <- liftTerm b
            return (Plus a' b')
        NApp (NApp (NCon (DC DC_mul) _) a _) b _ ->
            case (closedNat a, closedNat b) of
                (Just n, _) -> scaleTermRep n <$> liftTerm b
                (_, Just n) -> scaleTermRep n <$> liftTerm a
                _ -> fail_
        LVar lv -> do
            v <- allocL lv
            return (IVar v)
        _ -> fail_

closedNat :: TermNode -> Maybe Integer
closedNat t
    = case rewrite NF t of
        NCon (DC (DC_NatL n)) _
            | n >= 0 -> Just n
            | otherwise -> Nothing
        NApp (NCon (DC DC_Succ) _) a _ -> succ <$> closedNat a
        NApp (NApp (NCon (DC DC_plus) _) a _) b _ -> (+) <$> closedNat a <*> closedNat b
        NApp (NApp (NCon (DC DC_minus) _) a _) b _ -> do
            x <- closedNat a
            y <- closedNat b
            if x >= y then Just (x - y) else Nothing
        NApp (NApp (NCon (DC DC_mul) _) a _) b _ -> (*) <$> closedNat a <*> closedNat b
        NApp (NApp (NCon (DC DC_div) _) a _) b _ -> do
            x <- closedNat a
            y <- closedNat b
            if y == 0 then Nothing else Just (x `div` y)
        _ -> Nothing

scaleTermRep :: Integer -> PresburgerTermRep -> PresburgerTermRep
scaleTermRep n t
    | n <= 0 = Zero
    | n == 1 = t
    | otherwise = Plus t (scaleTermRep (n - 1) t)

renumberFormula :: Map.Map TermNode MyVar -> Map.Map MyVar TermNode -> MyPresburgerFormulaRep -> MyPresburgerFormulaRep
renumberFormula shared local rep = fst (goFormula startFresh Map.empty rep) where
    startFresh = maxMyVar (Map.elems shared) + 1
    maxMyVar :: [MyVar] -> MyVar
    maxMyVar = foldr max (theMinNumOfMyVar - 1)
    goFormula :: MyVar -> Map.Map MyVar MyVar -> MyPresburgerFormulaRep -> (MyPresburgerFormulaRep, MyVar)
    goFormula n _ (ValF b) = (ValF b, n)
    goFormula n env (EqnF t1 t2) = (EqnF (goTerm env t1) (goTerm env t2), n)
    goFormula n env (LtnF t1 t2) = (LtnF (goTerm env t1) (goTerm env t2), n)
    goFormula n env (LeqF t1 t2) = (LeqF (goTerm env t1) (goTerm env t2), n)
    goFormula n env (GtnF t1 t2) = (GtnF (goTerm env t1) (goTerm env t2), n)
    goFormula n env (ModF t1 r t2) = (ModF (goTerm env t1) r (goTerm env t2), n)
    goFormula n env (NegF f1) = (NegF f1', n1) where
        (f1', n1) = goFormula n env f1
    goFormula n env (DisF f1 f2) = (DisF f1' f2', n2) where
        (f1', n1) = goFormula n env f1
        (f2', n2) = goFormula n1 env f2
    goFormula n env (ConF f1 f2) = (ConF f1' f2', n2) where
        (f1', n1) = goFormula n env f1
        (f2', n2) = goFormula n1 env f2
    goFormula n env (ImpF f1 f2) = (ImpF f1' f2', n2) where
        (f1', n1) = goFormula n env f1
        (f2', n2) = goFormula n1 env f2
    goFormula n env (IffF f1 f2) = (IffF f1' f2', n2) where
        (f1', n1) = goFormula n env f1
        (f2', n2) = goFormula n1 env f2
    goFormula n env (AllF y f1) = (AllF y' f1', n1) where
        y' = n
        env' = Map.insert y y' env
        (f1', n1) = goFormula (n + 1) env' f1
    goFormula n env (ExsF y f1) = (ExsF y' f1', n1) where
        y' = n
        env' = Map.insert y y' env
        (f1', n1) = goFormula (n + 1) env' f1
    goTerm :: Map.Map MyVar MyVar -> PresburgerTermRep -> PresburgerTermRep
    goTerm env (IVar v)
        = case Map.lookup v env of
            Just v' -> IVar v'                  -- bound; α-renamed
            Nothing -> case Map.lookup v local of
                Just t -> case Map.lookup (rewrite NF t) shared of
                    Just v' -> IVar v'          -- free; mapped via shared
                    Nothing -> IVar v           -- fallback: leave as-is
                Nothing -> IVar v               -- unknown; leave as-is
    goTerm _ Zero
        = Zero
    goTerm env (Succ t)
        = Succ (goTerm env t)
    goTerm env (Plus t1 t2)
        = Plus (goTerm env t1) (goTerm env t2)

entails :: [MyPresburgerFormula] -> MyPresburgerFormula -> Bool
entails phis phi = checkTruthValueOfMyPresburgerFormula eliminated == Just True where
    hyp = foldr ConF (ValF True) phis
    body = ImpF hyp phi
    fvs = Set.toAscList (freeMyVarsF body)
    closed = foldr AllF body fvs
    eliminated = eliminateQuantifierReferringToTheBookWrittenByPeterHinman closed

arithEntails :: [TermNode] -> TermNode -> Bool
arithEntails hyps phi
    = case liftConstraint phi of
        Nothing -> False
        Just lrPhi -> entails compiledHyps compiledPhi where
            liftedHs = mapMaybe liftConstraint hyps
            allFreeTerms = Set.toAscList $ Set.union (Set.fromList (map (rewrite NF) (Map.elems (_freeOfLifted lrPhi)))) (Set.unions [ Set.fromList (map (rewrite NF) (Map.elems (_freeOfLifted h))) | h <- liftedHs ])
            shared = Map.fromAscList (zip allFreeTerms [theMinNumOfMyVar ..])
            phiRep = renumberFormula shared (_freeOfLifted lrPhi) (_liftedFormula lrPhi)
            hypReps = [ renumberFormula shared (_freeOfLifted h) (_liftedFormula h) | h <- liftedHs ]
            compiledPhi = fmap compilePresburgerTerm phiRep
            compiledHyps = map (fmap compilePresburgerTerm) hypReps

-- | Quantifier attached to a free atom when closing a presburger goal.
data FreeQuant
    = FQAll
    | FQExs
    deriving (Eq)

-- | Prenex ordering key for a free atom; smaller is more outer. @(0, 0)@ marks
--   top-level query variables (introduced before proof search). @(1, u)@ orders
--   by the creation 'unUnique' of a sigma/pi/clause variable, which is exactly
--   the proof-state introduction order.
type FreeKey = (Int, Int)

data LeafSt
    = LeafSt
        { leafInverse :: !(Map.Map TermNode MyVar)
        , leafTable :: !(Map.Map MyVar (FreeQuant, FreeKey))
        , leafNext :: !MyVar
        }

-- | An arithmetic store: comparison terms plus presburger formulas (each with
--   its own freeOf linking the formula's free variables to HOL terms).
type ArithStore = ([TermNode], [(MyPresburgerFormulaRep, Map.Map MyVar TermNode)])

-- | Close a constraint store into a single presburger formula under the
--   lia-style semantics, as @assumptions => obligations@.
--
--   Every free term is decomposed arithmetically (0/s/+/constant-scaling);
--   irreducible leaves are atomized to one fresh variable each (the same term
--   always reuses the same variable, across assumptions and obligations alike).
--   The formula @(/\\ assumptions) -> (/\\ obligations)@ is then closed with one
--   quantifier per atom:
--
--     * a logic variable (sigma\/query\/clause var) becomes existential,
--     * an eigenvariable (from @pi@) or an opaque non-linear term becomes
--       universal (treating it as uninterpreted - sound, possibly incomplete).
--
--   Quantifiers are ordered by the atom's introduction order so the prenex
--   respects the proof-state scoping (e.g. @sigma X\\ pi C\\@ closes to
--   @exists X. forall C.@, but @pi C\\ sigma X\\@ to @forall C. exists X.@).
--   Assumptions are the arithmetic facts in scope (the left-hand sides of @=>@);
--   obligations are the deferred goal constraints and the goal itself.
closeStore :: ArithStore -> ArithStore -> MyPresburgerFormula
closeStore assumptions obligations = fullyClosed where
    (body0, finalSt) = runState build (LeafSt Map.empty Map.empty theMinNumOfMyVar)
    build :: State LeafSt MyPresburgerFormulaRep
    build = do
        antecedent <- conjoinStore assumptions
        consequent <- conjoinStore obligations
        return (ImpF antecedent consequent)
    bodyC :: MyPresburgerFormula
    bodyC = fmap compilePresburgerTerm body0
    orderedLeaves :: [(MyVar, (FreeQuant, FreeKey))]
    orderedLeaves = List.sortBy (\p q -> compare (snd (snd p)) (snd (snd q))) (Map.toList (leafTable finalSt))
    closedC :: MyPresburgerFormula
    closedC = foldr wrap bodyC orderedLeaves where
        wrap (v, (FQAll, _)) acc = AllF v acc
        wrap (v, (FQExs, _)) acc = ExsF v acc
    -- Safety net: any stray free variable (should not arise for well-formed
    -- input) is universally closed, matching 'entails'.
    leftover :: [MyVar]
    leftover = Set.toAscList (freeMyVarsF bodyC `Set.difference` Map.keysSet (leafTable finalSt))
    fullyClosed :: MyPresburgerFormula
    fullyClosed = foldr AllF closedC leftover

-- | Is the constraint store satisfiable under its assumptions? Used both to
--   gate a @presburger@ goal (store conjoined with the new goal) and to prune
--   inconsistent branches.
presburgerStoreSat :: ArithStore -> ArithStore -> Bool
presburgerStoreSat assumptions obligations
    = checkTruthValueOfMyPresburgerFormula (eliminateQuantifierReferringToTheBookWrittenByPeterHinman (closeStore assumptions obligations)) == Just True

-- | Lift a store (comparisons + presburger formulas) into one conjunction,
--   atomizing free leaves into the shared 'LeafSt'.
conjoinStore :: ArithStore -> State LeafSt MyPresburgerFormulaRep
conjoinStore (cmpTerms, presForms) = do
    cmps <- mapM (leafFormula . rewrite NF) cmpTerms
    phis <- mapM (\(rep, freeOf) -> renumFormulaDecomp (Map.map (rewrite NF) freeOf) Map.empty rep) presForms
    return (foldr ConF (ValF True) ([ c | Just c <- cmps ] ++ phis))

-- | Do the assumptions entail the goal, i.e. is @(/\\ assumptions) -> phi@ valid
--   (true for all valuations)? A goal entailed by the in-scope @=>@ assumptions
--   is fully discharged and need not be retained as a residual.
presburgerEntails :: ArithStore -> (MyPresburgerFormulaRep, Map.Map MyVar TermNode) -> Bool
presburgerEntails assumptions (rep, freeOf)
    = checkTruthValueOfMyPresburgerFormula (eliminateQuantifierReferringToTheBookWrittenByPeterHinman validClosed) == Just True
    where
        (body0, _finalSt) = runState build (LeafSt Map.empty Map.empty theMinNumOfMyVar)
        build :: State LeafSt MyPresburgerFormulaRep
        build = do
            antecedent <- conjoinStore assumptions
            phi <- renumFormulaDecomp (Map.map (rewrite NF) freeOf) Map.empty rep
            return (ImpF antecedent phi)
        bodyC :: MyPresburgerFormula
        bodyC = fmap compilePresburgerTerm body0
        validClosed :: MyPresburgerFormula
        validClosed = foldr AllF bodyC (Set.toAscList (freeMyVarsF bodyC))

-- | A retained presburger constraint is redundant (carries no information) when
--   its universal closure already holds; such a residual can be dropped.
presburgerValid :: MyPresburgerFormulaRep -> Map.Map MyVar TermNode -> Bool
presburgerValid rep freeOf
    = checkTruthValueOfMyPresburgerFormula (eliminateQuantifierReferringToTheBookWrittenByPeterHinman validClosed) == Just True
    where
        (body0, _finalSt) = runState (renumFormulaDecomp (Map.map (rewrite NF) freeOf) Map.empty rep) (LeafSt Map.empty Map.empty theMinNumOfMyVar)
        bodyC :: MyPresburgerFormula
        bodyC = fmap compilePresburgerTerm body0
        validClosed :: MyPresburgerFormula
        validClosed = foldr AllF bodyC (Set.toAscList (freeMyVarsF bodyC))

-- | Renumber a parsed formula, α-renaming its own binders and splicing each
--   free reference's decomposed term (via 'leafTerm') in place.
renumFormulaDecomp :: Map.Map MyVar TermNode -> Map.Map MyVar MyVar -> MyPresburgerFormulaRep -> State LeafSt MyPresburgerFormulaRep
renumFormulaDecomp freeOf = go where
    go env f = case f of
        ValF b -> return (ValF b)
        EqnF a b -> EqnF <$> renumTermDecomp freeOf env a <*> renumTermDecomp freeOf env b
        LtnF a b -> LtnF <$> renumTermDecomp freeOf env a <*> renumTermDecomp freeOf env b
        LeqF a b -> LeqF <$> renumTermDecomp freeOf env a <*> renumTermDecomp freeOf env b
        GtnF a b -> GtnF <$> renumTermDecomp freeOf env a <*> renumTermDecomp freeOf env b
        ModF a r b -> (\a' b' -> ModF a' r b') <$> renumTermDecomp freeOf env a <*> renumTermDecomp freeOf env b
        NegF f1 -> NegF <$> go env f1
        DisF f1 f2 -> DisF <$> go env f1 <*> go env f2
        ConF f1 f2 -> ConF <$> go env f1 <*> go env f2
        ImpF f1 f2 -> ImpF <$> go env f1 <*> go env f2
        IffF f1 f2 -> IffF <$> go env f1 <*> go env f2
        AllF y f1 -> do { y' <- freshBound; AllF y' <$> go (Map.insert y y' env) f1 }
        ExsF y f1 -> do { y' <- freshBound; ExsF y' <$> go (Map.insert y y' env) f1 }

renumTermDecomp :: Map.Map MyVar TermNode -> Map.Map MyVar MyVar -> PresburgerTermRep -> State LeafSt PresburgerTermRep
renumTermDecomp freeOf env t = case t of
    IVar v -> case Map.lookup v env of
        Just v' -> return (IVar v')
        Nothing -> case Map.lookup v freeOf of
            Just term -> leafTerm term
            Nothing -> IVar <$> freshBound
    Zero -> return Zero
    Succ t1 -> Succ <$> renumTermDecomp freeOf env t1
    Plus t1 t2 -> Plus <$> renumTermDecomp freeOf env t1 <*> renumTermDecomp freeOf env t2

-- | Allocate a fresh bound variable (for a quantifier the source string itself
--   introduced); it is not recorded as a closable free atom.
freshBound :: State LeafSt MyVar
freshBound = do
    st <- get
    let v = leafNext st
    put st { leafNext = v + 1 }
    return v

-- | Intern a free atom, reusing the same variable for equal terms.
internAtom :: TermNode -> FreeQuant -> FreeKey -> State LeafSt MyVar
internAtom key quant order = do
    st <- get
    case Map.lookup key (leafInverse st) of
        Just v -> return v
        Nothing -> do
            let v = leafNext st
            put st
                { leafInverse = Map.insert key v (leafInverse st)
                , leafTable = Map.insert v (quant, order) (leafTable st)
                , leafNext = v + 1
                }
            return v

-- | Decompose a zonked nat term into a presburger term, atomizing leaves.
leafTerm :: TermNode -> State LeafSt PresburgerTermRep
leafTerm t = case t of
    NCon (DC (DC_NatL n)) _
        | n >= 0 -> return (natToTermRep n)
    NApp (NCon (DC DC_Succ) _) a _ -> Succ <$> leafTerm a
    NApp (NApp (NCon (DC DC_plus) _) a _) b _ -> Plus <$> leafTerm a <*> leafTerm b
    NApp (NApp (NCon (DC DC_mul) _) a _) b _
        | Just n <- closedNat a -> scaleTermRep n <$> leafTerm b
        | Just n <- closedNat b -> scaleTermRep n <$> leafTerm a
    LVar lv -> IVar <$> internAtom t FQExs (lvOrderKey lv)
    NCon (DC (DC_Unique uni _)) _ -> IVar <$> internAtom t FQAll (1, unUnique uni)
    _
        | Just n <- closedNat t -> return (natToTermRep n)
        | otherwise -> IVar <$> internAtom t FQAll (opaqueOrderKey t)

-- | A comparison hypothesis lifted into a formula, decomposing both sides; an
--   unrecognized constraint is dropped (Nothing), matching 'liftConstraint'.
leafFormula :: TermNode -> State LeafSt (Maybe MyPresburgerFormulaRep)
leafFormula t = case t of
    NApp (NApp (NApp (NCon (DC DC_eq) _) (NCon (TC (TC_Named "nat")) _) _) a _) b _ -> Just <$> (EqnF <$> leafTerm a <*> leafTerm b)
    NApp (NApp (NCon (DC DC_lt) _) a _) b _ -> Just <$> (LtnF <$> leafTerm a <*> leafTerm b)
    NApp (NApp (NCon (DC DC_le) _) a _) b _ -> Just <$> (LeqF <$> leafTerm a <*> leafTerm b)
    NApp (NApp (NCon (DC DC_gt) _) a _) b _ -> Just <$> (GtnF <$> leafTerm a <*> leafTerm b)
    NApp (NApp (NCon (DC DC_ge) _) a _) b _ -> Just <$> ((\a' b' -> NegF (LtnF a' b')) <$> leafTerm a <*> leafTerm b)
    _ -> return Nothing

-- | Introduction-order key of a logic variable.
lvOrderKey :: LogicVar -> FreeKey
lvOrderKey (LV_Named _) = (0, 0)
lvOrderKey (LV_Unique uni _) = (1, unUnique uni)
lvOrderKey (LV_ty_var uni) = (1, unUnique uni)

-- | Place an opaque atom just inside its constituents (max introduction key).
opaqueOrderKey :: TermNode -> FreeKey
opaqueOrderKey = foldr max (0, 0) . atomKeys where
    atomKeys :: TermNode -> [FreeKey]
    atomKeys (LVar lv) = [lvOrderKey lv]
    atomKeys (NCon (DC (DC_Unique uni _)) _) = [(1, unUnique uni)]
    atomKeys (NApp a b _) = atomKeys a ++ atomKeys b
    atomKeys _ = []

freeMyVarsF :: MyPresburgerFormula -> Set.Set MyVar
freeMyVarsF (ValF _) = Set.empty
freeMyVarsF (EqnF t1 t2) = freeMyVarsT t1 `Set.union` freeMyVarsT t2
freeMyVarsF (LtnF t1 t2) = freeMyVarsT t1 `Set.union` freeMyVarsT t2
freeMyVarsF (LeqF t1 t2) = freeMyVarsT t1 `Set.union` freeMyVarsT t2
freeMyVarsF (GtnF t1 t2) = freeMyVarsT t1 `Set.union` freeMyVarsT t2
freeMyVarsF (ModF t1 _ t2) = freeMyVarsT t1 `Set.union` freeMyVarsT t2
freeMyVarsF (NegF f1) = freeMyVarsF f1
freeMyVarsF (DisF f1 f2) = freeMyVarsF f1 `Set.union` freeMyVarsF f2
freeMyVarsF (ConF f1 f2) = freeMyVarsF f1 `Set.union` freeMyVarsF f2
freeMyVarsF (ImpF f1 f2) = freeMyVarsF f1 `Set.union` freeMyVarsF f2
freeMyVarsF (IffF f1 f2) = freeMyVarsF f1 `Set.union` freeMyVarsF f2
freeMyVarsF (AllF y f1) = Set.delete y (freeMyVarsF f1)
freeMyVarsF (ExsF y f1) = Set.delete y (freeMyVarsF f1)

freeMyVarsT :: PresburgerTerm -> Set.Set MyVar
freeMyVarsT (PresburgerTerm _ coeffs) = Map.keysSet (Map.filter (/= 0) coeffs)

installPresburger :: TermNode -> Either ErrMsg TermNode
installPresburger = installPresburgerWithEnv Map.empty

installPresburgerWithEnv :: Map.Map LargeId TermNode -> TermNode -> Either ErrMsg TermNode
installPresburgerWithEnv = go where
    placeholderSLoc :: SLoc
    placeholderSLoc = SLoc (0, 0) (0, 0)

    go :: Map.Map LargeId TermNode -> TermNode -> Either ErrMsg TermNode
    go env (NApp (NCon (DC (DC_Named "presburger")) _) arg sl)
        = case extractString arg of
            Just src -> do
                let litLoc = case sl of { Just l -> l; Nothing -> placeholderSLoc }
                r <- parsePresburger litLoc src env
                return (NPresburgerCheck (_formula r) (_freeOfFormula r) sl)
            Nothing -> Left
                (diagnosticNoLoc "HolBETA-PresburgerError" [Z.Doc.text "The argument must be a closed string literal."])
    go env (NApp t1 t2 sl) = do
        t1' <- go env t1
        t2' <- go env t2
        return (NApp t1' t2' sl)
    go env (NLam h ty t sl) = do
        t' <- go (enterLam h env) t
        return (NLam h ty t' sl)
    go env (Susp body ol nl senv) = do
        body' <- go env body
        senv' <- traverse (goSuspItem env) senv
        return (Susp body' ol nl senv')
    go _ t = return t

    enterLam :: Maybe SmallId -> Map.Map LargeId TermNode -> Map.Map LargeId TermNode
    enterLam mh env =
        case mh of
            Nothing -> shifted
            Just h -> Map.insert h (mkNIdx 0) shifted
        where
            shifted = Map.map (raiseIndices 0 1) env

    raiseIndices :: DeBruijn -> Int -> TermNode -> TermNode
    raiseIndices cutoff amount = goRaise cutoff where
        goRaise depth (LVar v) = mkLVar v
        goRaise depth (NCon c sl) = NCon c sl
        goRaise depth (NIdx i)
            | i >= depth = mkNIdx (i + amount)
            | otherwise = mkNIdx i
        goRaise depth (NApp t1 t2 sl) = NApp (goRaise depth t1) (goRaise depth t2) sl
        goRaise depth (NLam h ty body sl) = NLam h ty (goRaise (depth + 1) body) sl
        goRaise depth (Susp body ol nl senv) = Susp (goRaise depth body) ol nl (map (raiseSuspItem depth) senv)
        goRaise depth (NPresburgerCheck rep freeOf sl) = NPresburgerCheck rep (Map.map (goRaise depth) freeOf) sl

        raiseSuspItem depth (Dummy l) = Dummy l
        raiseSuspItem depth (Binds t l) = Binds (goRaise depth t) l

    goSuspItem :: Map.Map LargeId TermNode -> SuspItem -> Either ErrMsg SuspItem
    goSuspItem env (Dummy l) = return (Dummy l)
    goSuspItem env (Binds t l) = do
        t' <- go env t
        return (Binds t' l)
    extractString :: TermNode -> Maybe String
    extractString (NApp (NCon (DC DC_Nil) _) _ _) = Just ""
    extractString (NApp (NApp (NApp (NCon (DC DC_Cons) _) _typeArg _) (NCon (DC (DC_ChrL c)) _) _) rest _) = do
        cs <- extractString rest
        return (c : cs)
    extractString _ = Nothing
