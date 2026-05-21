module Hol.BETA2.Arith
    ( ParseResult (..)
    , LiftResult (..)
    , parsePresburger
    , zonkPresburger
    , liftConstraint
    , renumberFormula
    , entails
    , arithEntails
    , installPresburger
    ) where

import Calc.Presburger.Internal
import Data.Char (isAlphaNum, isDigit, isSpace)
import qualified Data.List as List
import qualified Data.Map.Strict as Map
import Data.Maybe (mapMaybe)
import qualified Data.Set as Set
import Hol.BETA2.Constant
import Hol.BETA2.Diagnostic
import Hol.BETA2.Header
import Hol.BETA2.TermNode
import qualified Z.Doc
import Z.Utils (ErrMsg)


data ParseResult
    = ParseResult
    { _formula :: MyPresburgerFormulaRep
    , _freeOfFormula :: Map.Map MyVar LogicVar
    , _updatedEnv :: Map.Map LargeId LogicVar
    } deriving ()

data LiftResult
    = LiftResult
    { _liftedFormula :: MyPresburgerFormulaRep
    , _freeOfLifted :: Map.Map MyVar LogicVar
    } deriving ()


parsePresburger :: SLoc -> String -> Map.Map LargeId LogicVar -> Either ErrMsg ParseResult
parsePresburger sloc src env0
    = case runP parseTop initState of
        Left msg       -> Left (locPrefix ++ msg)
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
    , psNameToVar :: !(Map.Map LargeId LogicVar)
    , psBoundStack :: ![(LargeId, MyVar)]
    , psFreeMap :: !(Map.Map MyVar LogicVar)
    , psInverseFree :: !(Map.Map LogicVar MyVar)
    , psNextVar :: !MyVar
    } deriving ()

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
                Just lv -> reuseOrAlloc lv
                Nothing -> do
                    let lv = LV_Named name
                    modify $ \s -> s { psNameToVar = Map.insert name lv (psNameToVar s) }
                    reuseOrAlloc lv
    where
        reuseOrAlloc lv = do
            st <- getState
            case Map.lookup lv (psInverseFree st) of
                Just v -> return v
                Nothing -> do
                    let v = psNextVar st
                    modify $ \s -> s { psFreeMap = Map.insert v lv (psFreeMap s) , psInverseFree = Map.insert lv v (psInverseFree s) , psNextVar = v + 1 }
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
        ('(' : _) -> do
            mustLiteral "("
            t <- parseArith
            mustLiteral ")"
            return t
        (c : _)
            | isDigit c -> do
                mn <- decimalNat
                case mn of
                    Just n -> return (natToTermRep n)
                    Nothing -> throwP "expected decimal literal"
        (c : _)
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
        ('<' : '-' : '>' : rest) -> do
            setInput rest
            f2 <- parseLevel0
            return (IffF f1 f2)
        ('-' : '>' : rest) -> do
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
                ('\\' : '/' : more) -> do
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
                ('/' : '\\' : more) -> do
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
            ('~' : rest) -> do
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
        keywordAt kw s =
            kw `List.isPrefixOf` s &&
            case drop (length kw) s of
                [] -> True
                (c : _) -> not (isIdentCont c)

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
        ('_' : '|' : '_' : rest) -> do
            setInput rest
            return (ValF False)
        ('(' : _) -> do
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
        ('=' : '<' : rest) -> do
            setInput rest
            t2 <- parseArith
            return (LeqF t1 t2)
        ('=' : '=' : '_' : '{' : rest) -> do
            setInput rest
            mn <- decimalNat
            mustLiteral "}"
            t2 <- parseArith
            case mn of
                Just n
                    | n > 0 -> return (ModF t1 (fromInteger n) t2)
                _ -> throwP "modulus must be a positive decimal literal"
        ('=' : rest) -> do
            setInput rest
            t2 <- parseArith
            return (EqnF t1 t2)
        ('<' : rest) -> do
            setInput rest
            t2 <- parseArith
            return (LtnF t1 t2)
        ('>' : '=' : rest) -> do
            setInput rest
            t2 <- parseArith
            return (NegF (LtnF t1 t2))
        ('>' : rest) -> do
            setInput rest
            t2 <- parseArith
            return (GtnF t1 t2)
        _ -> throwP ("expected a relational operator, got: " ++ shows (take 20 inp) "")


zonkPresburger :: (LogicVar -> Maybe TermNode) -> Map.Map MyVar LogicVar -> MyPresburgerFormulaRep -> MyPresburgerFormulaRep
zonkPresburger theta freeOf = goFormula Set.empty where
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
        | v `Set.member` bound = IVar v
        | otherwise = case Map.lookup v freeOf of
            Just lv -> case theta lv of
                Just t -> case asClosedNatLit t of
                    Just n -> natToTermRep n
                    Nothing -> IVar v
                Nothing -> IVar v
            Nothing -> IVar v
    goTerm _ Zero = Zero
    goTerm bound (Succ t) = Succ (goTerm bound t)
    goTerm bound (Plus t1 t2) = Plus (goTerm bound t1) (goTerm bound t2)

    asClosedNatLit :: TermNode -> Maybe Integer
    asClosedNatLit (NCon (DC (DC_NatL n)) _) = Just n
    asClosedNatLit _ = Nothing


liftConstraint :: TermNode -> Maybe LiftResult
liftConstraint t
    = case runLift (liftFormula t) emptyLS of
        Just (f, st) -> Just LiftResult
            { _liftedFormula = f
            , _freeOfLifted = lsFreeMap st
            }
        Nothing -> Nothing
    where
        emptyLS = LiftState
            { lsFreeMap = Map.empty
            , lsInverse = Map.empty
            , lsNextVar = theMinNumOfMyVar
            }

data LiftState
    = LiftState
    { lsFreeMap :: !(Map.Map MyVar LogicVar)
    , lsInverse :: !(Map.Map LogicVar MyVar)
    , lsNextVar :: !MyVar
    } deriving ()

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
    return = pure
    L g >>= k = L $ \s -> case g s of
        Nothing -> Nothing
        Just (a, s') -> runLift (k a) s'

fail_ :: L a
fail_ = L $ \_ -> Nothing

allocL :: LogicVar -> L MyVar
allocL lv
    = L $ \s -> case Map.lookup lv (lsInverse s) of
        Just v -> Just (v, s)
        Nothing -> Just (v, s') where
            v = lsNextVar s
            s' = s
                { lsFreeMap = Map.insert v lv (lsFreeMap s)
                , lsInverse = Map.insert lv v (lsInverse s)
                , lsNextVar = v + 1
                }

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
liftTerm t = case t of
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
closedNat t = case rewrite NF t of
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


renumberFormula :: Map.Map LogicVar MyVar -> Map.Map MyVar LogicVar -> MyPresburgerFormulaRep -> MyPresburgerFormulaRep
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
                Just lv -> case Map.lookup lv shared of
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
            allLVs = Set.toAscList $ Set.union (Set.fromList (Map.elems (_freeOfLifted lrPhi))) (Set.unions [ Set.fromList (Map.elems (_freeOfLifted h)) | h <- liftedHs ])
            shared = Map.fromAscList (zip allLVs [theMinNumOfMyVar ..])
            phiRep = renumberFormula shared (_freeOfLifted lrPhi) (_liftedFormula lrPhi)
            hypReps = [ renumberFormula shared (_freeOfLifted h) (_liftedFormula h) | h <- liftedHs ]
            compiledPhi = fmap compilePresburgerTerm phiRep
            compiledHyps = map (fmap compilePresburgerTerm) hypReps

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
installPresburger = go where
    placeholderSLoc :: SLoc
    placeholderSLoc = SLoc (0, 0) (0, 0)

    go :: TermNode -> Either ErrMsg TermNode
    go (NApp (NCon (DC (DC_Named "presburger")) _) arg sl)
        = case extractString arg of
            Just src -> do
                let litLoc = case sl of { Just l -> l; Nothing -> placeholderSLoc }
                r <- parsePresburger litLoc src Map.empty
                return (NPresburgerCheck (_formula r) (_freeOfFormula r) sl)
            Nothing -> Left
                (diagnosticNoLoc "HolBETA2-PresburgerError" [Z.Doc.text "The argument must be a closed string literal."])
    go (NApp t1 t2 sl) = do
        t1' <- go t1
        t2' <- go t2
        return (NApp t1' t2' sl)
    go (NLam h ty t sl) = do
        t' <- go t
        return (NLam h ty t' sl)
    go (Susp body ol nl env) = do
        body' <- go body
        env' <- traverse goSuspItem env
        return (Susp body' ol nl env')
    go t = return t

    goSuspItem :: SuspItem -> Either ErrMsg SuspItem
    goSuspItem (Dummy l) = return (Dummy l)
    goSuspItem (Binds t l) = do
        t' <- go t
        return (Binds t' l)

    extractString :: TermNode -> Maybe String
    extractString (NApp (NCon (DC DC_Nil) _) _ _) = Just ""
    extractString (NApp (NApp (NApp (NCon (DC DC_Cons) _) _typeArg _) (NCon (DC (DC_ChrL c)) _) _) rest _) = do
        cs <- extractString rest
        return (c : cs)
    extractString _ = Nothing
