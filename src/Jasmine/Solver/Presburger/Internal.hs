module Jasmine.Solver.Presburger.Internal where

import qualified Data.List as List
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Y.Base
import Z.Algo.Function
import Z.Utils

type MyVar = PositiveInteger

type MyCoefficient = PositiveInteger

type MyPresburgerFormula = PresburgerFormula PresburgerTerm

type MyPresburgerFormulaRep = PresburgerFormula PresburgerTermRep

type MyCoefficientEnvironmentOfMyVar = Map.Map MyVar MyCoefficient

type MyProp = Bool

data PresburgerTerm
    = PresburgerTerm 
        { getConstantTerm :: !(MyNat)
        , getCoefficients :: !(MyCoefficientEnvironmentOfMyVar)
        }
    deriving (Eq)

data PresburgerFormula term
    = ValF (MyProp)
    | EqnF (term) (term)
    | LtnF (term) (term)
    | LeqF (term) (term)
    | GtnF (term) (term)
    | ModF (term) (PositiveInteger) (term)
    | NegF (PresburgerFormula term)
    | DisF (PresburgerFormula term) (PresburgerFormula term)
    | ConF (PresburgerFormula term) (PresburgerFormula term)
    | ImpF (PresburgerFormula term) (PresburgerFormula term)
    | IffF (PresburgerFormula term) (PresburgerFormula term)
    | AllF (MyVar) (PresburgerFormula term)
    | ExsF (MyVar) (PresburgerFormula term)
    deriving (Eq)

data PresburgerKlass
    = KlassEqn !(MyCoefficient) !(PresburgerTerm) !(PresburgerTerm)
    | KlassLtn !(MyCoefficient) !(PresburgerTerm) !(PresburgerTerm)
    | KlassGtn !(MyCoefficient) !(PresburgerTerm) !(PresburgerTerm)
    | KlassMod !(MyCoefficient) !(PresburgerTerm) (PositiveInteger) !(PresburgerTerm)
    | KlassEtc !(MyPresburgerFormula)
    deriving (Eq, Show)

data PresburgerTermRep
    = IVar (MyVar)
    | Zero
    | Succ (PresburgerTermRep)
    | Plus (PresburgerTermRep) (PresburgerTermRep)
    deriving (Eq)

data CollectionOfProperKlasses
    = CollectionOfProperKlasses
        { _Eqns :: [(PresburgerTerm, PresburgerTerm)]
        , _Ltns :: [(PresburgerTerm, PresburgerTerm)]
        , _Gtns :: [(PresburgerTerm, PresburgerTerm)]
        , _Mods :: [(PositiveInteger, (PresburgerTerm, PresburgerTerm))]
        , _TheR :: !(PositiveInteger)
        }
    deriving (Show)

instance Show (PresburgerTerm) where
    showsPrec 0 (PresburgerTerm con coeffs)
        | Map.null coeffs = shows con
        | otherwise = strcat
            [ ppunc " + "
                [ case coeff of
                    1 -> showsMyVar var
                    n -> strcat
                        [ if n < 0 then strstr "(" . shows n . strstr ")" else shows n
                        , strstr " " . showsMyVar var
                        ]
                | (var, coeff) <- Map.toAscList coeffs
                ]
            , case con `compare` 0 of
                (LT) -> strstr " - " . shows (abs con)
                (EQ) -> id
                (GT) -> strstr " + " . shows (abs con)
            ]
    showsPrec prec t = if prec >= 5 then strstr "(" . showsPrec 0 t . strstr ")" else showsPrec 0 t

instance Show term => Show (PresburgerFormula term) where
    showsPrec prec = dispatch where
        myPrecIs :: Precedence -> ShowS -> ShowS
        myPrecIs prec' ss = if prec > prec' then strstr "(" . ss . strstr ")" else ss
        dispatch :: Show term => PresburgerFormula term -> ShowS
        dispatch (ValF b) = myPrecIs 4 $ strstr (if b then "~ _|_" else "_|_")
        dispatch (EqnF t1 t2) = myPrecIs 4 $ shows t1 . strstr " = " . shows t2
        dispatch (LtnF t1 t2) = myPrecIs 4 $ shows t1 . strstr " < " . shows t2
        dispatch (LeqF t1 t2) = myPrecIs 4 $ shows t1 . strstr " =< " . shows t2
        dispatch (GtnF t1 t2) = myPrecIs 4 $ shows t1 . strstr " > " . shows t2
        dispatch (ModF t1 r t2) = myPrecIs 4 $ shows t1 . strstr " ==_{" . shows r . strstr "} " . shows t2
        dispatch (NegF f1) = myPrecIs 3 $ strstr "~ " . showsPrec 4 f1
        dispatch (DisF f1 f2) = myPrecIs 1 $ showsPrec 1 f1 . strstr " \\/ " . showsPrec 2 f2
        dispatch (ConF f1 f2) = myPrecIs 2 $ showsPrec 3 f1 . strstr " /\\ " . showsPrec 2 f2
        dispatch (ImpF f1 f2) = myPrecIs 0 $ showsPrec 1 f1 . strstr " -> " . showsPrec 0 f2
        dispatch (IffF f1 f2) = myPrecIs 0 $ showsPrec 1 f1 . strstr " <-> " . showsPrec 1 f2
        dispatch (AllF y f1) = myPrecIs 3 $ strstr "forall " . showsMyVar y . strstr ", " . showsPrec 3 f1
        dispatch (ExsF y f1) = myPrecIs 3 $ strstr "exists " . showsMyVar y . strstr ", " . showsPrec 3 f1

instance Show (PresburgerTermRep) where
    showsPrec prec = dispatch where
        myPrecIs :: Precedence -> ShowS -> ShowS
        myPrecIs prec' ss = if prec > prec' then strstr "(" . ss . strstr ")" else ss
        dispatch :: PresburgerTermRep -> ShowS
        dispatch (IVar x) = myPrecIs 2 $ showsMyVar x
        dispatch (Zero) = myPrecIs 2 $ strstr "O"
        dispatch (Succ t1) = myPrecIs 1 $ strstr "S " . showsPrec 2 t1
        dispatch (Plus t1 t2) = myPrecIs 0 $ showsPrec 0 t1 . strstr " + " . showsPrec 1 t2

instance Functor (PresburgerFormula) where
    fmap = callWithStrictArg (flip go) where
        go :: PresburgerFormula old_term -> (old_term -> term) -> PresburgerFormula term
        go (ValF b) = pure ValF <*> pure b
        go (EqnF t1 t2) = pure EqnF <*> flip callWithStrictArg t1 <*> flip callWithStrictArg t2
        go (LtnF t1 t2) = pure LtnF <*> flip callWithStrictArg t1 <*> flip callWithStrictArg t2
        go (LeqF t1 t2) = pure LeqF <*> flip callWithStrictArg t1 <*> flip callWithStrictArg t2
        go (GtnF t1 t2) = pure GtnF <*> flip callWithStrictArg t1 <*> flip callWithStrictArg t2
        go (ModF t1 r t2) = pure ModF <*> flip callWithStrictArg t1 <*> pure r <*> flip callWithStrictArg t2
        go (NegF f1) = pure NegF <*> flip fmap f1
        go (DisF f1 f2) = pure DisF <*> flip fmap f1 <*> flip fmap f2
        go (ConF f1 f2) = pure ConF <*> flip fmap f1 <*> flip fmap f2
        go (ImpF f1 f2) = pure ImpF <*> flip fmap f1 <*> flip fmap f2
        go (IffF f1 f2) = pure IffF <*> flip fmap f1 <*> flip fmap f2
        go (AllF y f1) = pure AllF <*> pure y <*> flip fmap f1
        go (ExsF y f1) = pure ExsF <*> pure y <*> flip fmap f1

theMinNumOfMyVar :: MyVar
theMinNumOfMyVar = 1

showsMyVar :: MyVar -> ShowS
showsMyVar x
    | x >= theMinNumOfMyVar = strstr "v" . shows x
    | otherwise = strstr "?v" . (if x > 0 then id else strstr "_") . shows (abs x)

areCongruentModulo :: MyNat -> PositiveInteger -> MyNat -> MyProp
areCongruentModulo n1 r n2 = if r > 0 then n1 `mod` r == n2 `mod` r else error "areCongruentModulo: r must be positive"

plusCoeffs :: MyCoefficientEnvironmentOfMyVar -> MyCoefficientEnvironmentOfMyVar -> MyCoefficientEnvironmentOfMyVar
plusCoeffs = Map.foldrWithKey $ \var -> \coeff -> Map.alter (maybe (callWithStrictArg Just coeff) (\coeff' -> callWithStrictArg Just (coeff + coeff'))) var

compilePresburgerTerm :: PresburgerTermRep -> PresburgerTerm
compilePresburgerTerm = fromTermRep where
    fromTermRep :: PresburgerTermRep -> PresburgerTerm
    fromTermRep (IVar x) = mkIVar x
    fromTermRep (Zero) = mkZero
    fromTermRep (Succ t1) = mkSucc (fromTermRep t1)
    fromTermRep (Plus t1 t2) = mkPlus (fromTermRep t1) (fromTermRep t2)
    mkIVar :: MyVar -> PresburgerTerm
    mkIVar x = PresburgerTerm { getConstantTerm = 0, getCoefficients = Map.singleton x 1 }
    mkZero :: PresburgerTerm
    mkZero = PresburgerTerm { getConstantTerm = 0, getCoefficients = Map.empty }
    mkSucc :: PresburgerTerm -> PresburgerTerm
    mkSucc (PresburgerTerm con1 coeffs1) = PresburgerTerm { getConstantTerm = succ con1, getCoefficients = coeffs1 } 
    mkPlus :: PresburgerTerm -> PresburgerTerm -> PresburgerTerm
    mkPlus (PresburgerTerm con1 coeffs1) (PresburgerTerm con2 coeffs2) = PresburgerTerm { getConstantTerm = con1 + con2, getCoefficients = plusCoeffs coeffs1 coeffs2 }

eliminateQuantifierReferringToTheBookWrittenByPeterHinman :: MyPresburgerFormula -> MyPresburgerFormula
eliminateQuantifierReferringToTheBookWrittenByPeterHinman = asterify . simplify where
    simplify :: MyPresburgerFormula -> MyPresburgerFormula
    simplify (ValF b) = mkValF b
    simplify (EqnF t1 t2) = mkEqnF t1 t2
    simplify (LtnF t1 t2) = mkLtnF t1 t2
    simplify (LeqF t1 t2) = mkLeqF t1 t2
    simplify (GtnF t1 t2) = mkGtnF t1 t2
    simplify (ModF t1 r t2) = mkModF t1 r t2
    simplify (NegF f1) = mkNegF (simplify f1)
    simplify (DisF f1 f2) = mkDisF (simplify f1) (simplify f2)
    simplify (ConF f1 f2) = mkConF (simplify f1) (simplify f1)
    simplify (ImpF f1 f2) = mkImpF (simplify f1) (simplify f2)
    simplify (IffF f1 f2) = mkIffF (simplify f1) (simplify f2)
    simplify (AllF y f1) = mkAllF y (simplify f1)
    simplify (ExsF y f1) = mkExsF y (simplify f1)
    asterify :: MyPresburgerFormula -> MyPresburgerFormula
    asterify (NegF f1) = mkNegF (asterify f1)
    asterify (ConF f1 f2) = mkConF (asterify f1) (asterify f2)
    asterify (DisF f1 f2) = mkDisF (asterify f1) (asterify f2)
    asterify (ExsF y f1) = eliminateExsF y (asterify f1)
    asterify f = f
    eliminateExsF :: MyVar -> MyPresburgerFormula -> MyPresburgerFormula
    eliminateExsF = curry $ (orcat . uncurry callWithStrictArg) . (map . curry (step3 . uncurry step2) <^> step1) where
        step1 :: MyPresburgerFormula -> [[MyPresburgerFormula]]
        step1 = makeDNF . eliminateNegF where
            runNegation :: MyPresburgerFormula -> MyPresburgerFormula
            runNegation (ValF b) = mkValF (not b)
            runNegation (EqnF t1 t2) = mkDisF (mkLtnF t1 t2) (mkGtnF t1 t2)
            runNegation (LtnF t1 t2) = mkDisF (mkEqnF t1 t2) (mkGtnF t1 t2)
            runNegation (ModF t1 r t2) = orcat [ mkModF t1 r (mkPlus t2 (mkNum i)) | i <- [1 .. r - 1] ]
            runNegation (NegF f1) = f1
            runNegation (DisF f1 f2) = mkConF (runNegation f1) (runNegation f2)
            runNegation (ConF f1 f2) = mkDisF (runNegation f1) (runNegation f2)
            eliminateNegF :: MyPresburgerFormula -> MyPresburgerFormula
            eliminateNegF (NegF f1) = runNegation (eliminateNegF f1)
            eliminateNegF (DisF f1 f2) = mkDisF (eliminateNegF f1) (eliminateNegF f2)
            eliminateNegF (ConF f1 f2) = mkConF (eliminateNegF f1) (eliminateNegF f2)
            eliminateNegF f = f
            makeDNF :: MyPresburgerFormula -> [[MyPresburgerFormula]]
            makeDNF (ValF b) = if b then pure [] else []
            makeDNF (DisF f1 f2) = makeDNF f1 ++ makeDNF f2
            makeDNF (ConF f1 f2) = pure (++) <*> makeDNF f1 <*> makeDNF f2
            makeDNF f = [one f]
        step2 :: MyVar -> [MyPresburgerFormula] -> ([PresburgerKlass], [PositiveInteger])
        step2 x = (curry id <*> collectCoefficients) . map toKlass where
            extractCoefficient :: PresburgerTerm -> (MyCoefficient, PresburgerTerm)
            extractCoefficient t = maybe (0, t) (\n -> (n, PresburgerTerm (getConstantTerm t) (Map.delete x (getCoefficients t)))) (Map.lookup x (getCoefficients t))
            toKlass :: MyPresburgerFormula -> PresburgerKlass
            toKlass (EqnF t1 t2) = forEqnF (extractCoefficient t1) (extractCoefficient t2)
            toKlass (LtnF t1 t2) = forLtnF (extractCoefficient t1) (extractCoefficient t2)
            toKlass (ModF t1 r t2) = forModF (extractCoefficient t1) r (extractCoefficient t2)
            forEqnF :: (MyCoefficient, PresburgerTerm) -> (MyCoefficient, PresburgerTerm) -> PresburgerKlass
            forEqnF (m1, t1) (m2, t2)
                = case m1 `compare` m2 of
                    (LT) -> KlassEqn (m2 - m1) t2 t1
                    (EQ) -> KlassEtc (mkEqnF t1 t2)
                    (GT) -> KlassEqn (m1 - m2) t1 t2
            forLtnF :: (MyCoefficient, PresburgerTerm) -> (MyCoefficient, PresburgerTerm) -> PresburgerKlass
            forLtnF (m1, t1) (m2, t2)
                = case m1 `compare` m2 of
                    (LT) -> KlassGtn (m2 - m1) t2 t1
                    (EQ) -> KlassEtc (mkLtnF t1 t2)
                    (GT) -> KlassLtn (m1 - m2) t1 t2
            forModF :: (MyCoefficient, PresburgerTerm) -> PositiveInteger -> (MyCoefficient, PresburgerTerm) -> PresburgerKlass
            forModF (m1, t1) r (m2, t2)
                = case m1 `compare` m2 of
                    (LT) -> KlassMod (m2 - m1) t2 r t1
                    (EQ) -> KlassEtc (mkModF t1 r t2)
                    (GT) -> KlassMod (m1 - m2) t1 r t2
            collectCoefficients :: [PresburgerKlass] -> [PositiveInteger]
            collectCoefficients klasses = do
                klass <- klasses
                case klass of
                    (KlassEqn m t1 t2) -> return m
                    (KlassLtn m t1 t2) -> return m
                    (KlassGtn m t1 t2) -> return m
                    (KlassMod m t1 r t2) -> return m
                    (KlassEtc f) -> []
        step3 :: ([PresburgerKlass], [PositiveInteger]) -> MyPresburgerFormula
        step3 = andcatKlasses . fst <*> null . snd <*> List.foldl' getGCD 1 . snd where
            andcatKlasses :: [PresburgerKlass] -> Bool -> PositiveInteger -> MyPresburgerFormula
            andcatKlasses yourKlasses isTrivialCase yourLCM = andcat (if isTrivialCase then yourEtcs else (yourLCM `seq` hisMethod myProperKlasses) : yourEtcs) where
                myEqns :: [(PresburgerTerm, PresburgerTerm)]
                myEqns = [ (multiplication (yourLCM `div` m) t1, multiplication (yourLCM `div` m) t2) | (KlassEqn m t1 t2) <- yourKlasses ]
                myLtns :: [(PresburgerTerm, PresburgerTerm)]
                myLtns = [ (multiplication (yourLCM `div` m) t1, multiplication (yourLCM `div` m) t2) | (KlassLtn m t1 t2) <- yourKlasses ]
                myGtns :: [(PresburgerTerm, PresburgerTerm)]
                myGtns = (mkNum 1, mkNum 0) : [ (multiplication (yourLCM `div` m) t1, multiplication (yourLCM `div` m) t2) | (KlassGtn m t1 t2) <- yourKlasses ]
                myMods :: [(PositiveInteger, (PresburgerTerm, PresburgerTerm))]
                myMods = (yourLCM, (mkNum 0, mkNum 0)) : [ ((yourLCM `div` m) * r, (multiplication (yourLCM `div` m) t1, multiplication (yourLCM `div` m) t2)) | (KlassMod m t1 r t2) <- yourKlasses ]
                yourEtcs :: [MyPresburgerFormula]
                yourEtcs = [ f | (KlassEtc f) <- yourKlasses ]
                myProperKlasses :: CollectionOfProperKlasses
                myProperKlasses = CollectionOfProperKlasses
                    { _Eqns = myEqns
                    , _Ltns = myLtns
                    , _Gtns = myGtns
                    , _Mods = myMods
                    , _TheR = List.foldl' getLCM 1 (map fst myMods)
                    }
            hisMethod :: CollectionOfProperKlasses -> MyPresburgerFormula
            hisMethod (CollectionOfProperKlasses theEqns0 theLtns0 theGtns0 theMods0 theR)
                = case theEqns0 of
                    [] -> orcat
                        [ andcat
                            [ andcat [ mkLeqF (mkPlus u' _u) (mkPlus u _u') | (_u, _u') <- theLtns0 ]
                            , andcat [ mkLeqF (mkPlus v' _v) (mkPlus v _v') | (_v', _v) <- theGtns0 ]
                            , orcat
                                [ andcat
                                    [ mkLtnF (mkPlus u (mkPlus v (mkNum s))) (mkPlus u' v')
                                    , andcat [ mkModF (mkPlus v (mkPlus (mkNum s) w)) r (mkPlus v' w') | (r, (w, w')) <- theMods0 ]
                                    ]
                                | s <- [1 .. theR]
                                ]
                            ]
                        | (u, u') <- theLtns0
                        , (v', v) <- theGtns0
                        ]
                    ((t1, t2) : theEqns1) -> andcat
                        [ andcat [ mkEqnF (mkPlus t2 t) (mkPlus t' t1) | (t, t') <- theEqns1 ]
                        , andcat [ mkLtnF (mkPlus t2 u) (mkPlus u' t1) | (u, u') <- theLtns0 ]
                        , andcat [ mkGtnF (mkPlus t2 v) (mkPlus v' t1) | (v, v') <- theGtns0 ]
                        , andcat [ mkModF (mkPlus t2 w) r (mkPlus w' t1) | (r, (w, w')) <- theMods0 ]
                        ]
    mkNum :: MyNat -> PresburgerTerm
    mkNum k = PresburgerTerm { getConstantTerm = k, getCoefficients = Map.empty } 
    mkPlus :: PresburgerTerm -> PresburgerTerm -> PresburgerTerm
    mkPlus (PresburgerTerm con1 coeffs1) (PresburgerTerm con2 coeffs2) = PresburgerTerm { getConstantTerm = con1 + con2, getCoefficients = plusCoeffs coeffs1 coeffs2 }
    orcat :: [MyPresburgerFormula] -> MyPresburgerFormula
    orcat = List.foldl' mkDisF (mkValF False)
    andcat :: [MyPresburgerFormula] -> MyPresburgerFormula
    andcat = foldr mkConF (mkValF True)
    mkValF :: MyProp -> MyPresburgerFormula
    mkValF b = b `seq` ValF b
    mkEqnF :: PresburgerTerm -> PresburgerTerm -> MyPresburgerFormula
    mkEqnF t1 t2 = if getCoefficients t1 == getCoefficients t2 then mkValF (getConstantTerm t1 == getConstantTerm t2) else EqnF t1 t2
    mkLtnF :: PresburgerTerm -> PresburgerTerm -> MyPresburgerFormula
    mkLtnF t1 t2 = if getCoefficients t1 == getCoefficients t2 then mkValF (getConstantTerm t1 < getConstantTerm t2) else LtnF t1 t2
    mkLeqF :: PresburgerTerm -> PresburgerTerm -> MyPresburgerFormula
    mkLeqF t1 t2 = mkDisF (mkEqnF t1 t2) (mkLtnF t1 t2)
    mkGtnF :: PresburgerTerm -> PresburgerTerm -> MyPresburgerFormula
    mkGtnF t1 t2 = mkLtnF t2 t1
    mkModF :: PresburgerTerm -> PositiveInteger -> PresburgerTerm -> MyPresburgerFormula
    mkModF t1 r t2 = if r > 0 then congruence (modify t1) r (modify t2) else error "mkModF: r must be positive" where
        modify :: PresburgerTerm -> PresburgerTerm
        modify (PresburgerTerm con coeffs) = PresburgerTerm { getConstantTerm = con `mod` r, getCoefficients = Map.fromAscList [ (x, n `mod` r) | (x, n) <- Map.toAscList coeffs, n `mod` r /= 0 ] }
    mkNegF :: MyPresburgerFormula -> MyPresburgerFormula
    mkNegF (ValF b) = mkValF (not b)
    mkNegF (NegF f1) = f1
    mkNegF f1 = NegF f1
    mkDisF :: MyPresburgerFormula -> MyPresburgerFormula -> MyPresburgerFormula
    mkDisF f1 f2 = fromJust (trick f1 (f1, f2) /> trick f2 (f2, f1) /> Just (DisF f1 f2))
    mkConF :: MyPresburgerFormula -> MyPresburgerFormula -> MyPresburgerFormula
    mkConF f1 f2 = fromJust (trick f2 (f1, f2) /> trick f1 (f2, f1) /> Just (ConF f1 f2))
    mkImpF :: MyPresburgerFormula -> MyPresburgerFormula -> MyPresburgerFormula
    mkImpF f1 f2 = mkDisF (mkNegF f1) f2
    mkIffF :: MyPresburgerFormula -> MyPresburgerFormula -> MyPresburgerFormula
    mkIffF f1 f2 = mkConF (mkImpF f1 f2) (mkImpF f2 f1)
    mkAllF :: MyVar -> MyPresburgerFormula -> MyPresburgerFormula
    mkAllF y f1 = mkNegF (mkExsF y (mkNegF f1))
    mkExsF :: MyVar -> MyPresburgerFormula -> MyPresburgerFormula
    mkExsF y f1 = f1 `seq` ExsF y f1
    multiplication :: MyNat -> PresburgerTerm -> PresburgerTerm
    multiplication k t
        | k >= 0 = if k == 1 then t else PresburgerTerm (getConstantTerm t * k) (Map.map (\n -> n * k) (getCoefficients t))
        | otherwise = error "multiplication: negative input"
    congruence :: PresburgerTerm -> PositiveInteger -> PresburgerTerm -> MyPresburgerFormula
    congruence t1 r t2
        | r > 0 = if getCoefficients t1 == getCoefficients t2 then mkValF (areCongruentModulo (getConstantTerm t1) r (getConstantTerm t2)) else ModF t1 r t2
        | otherwise = error "congruence: r must be positive"
    getLCM :: PositiveInteger -> PositiveInteger -> PositiveInteger
    getLCM k1 k2 = maybe ((k1 * k2) `div` (getGCD k1 k2)) id (lookup 1 [(k1, k2), (k2, k1)])
    trick :: MyPresburgerFormula -> (MyPresburgerFormula, MyPresburgerFormula) -> Maybe MyPresburgerFormula
    trick (ValF b) = if b then pure . fst else pure . snd
    trick _ = pure Nothing

checkTruthValueOfMyPresburgerFormula :: MyPresburgerFormula -> Maybe MyProp
checkTruthValueOfMyPresburgerFormula = tryEvalFormula where
    tryEvalTerm :: PresburgerTerm -> Maybe MyNat
    tryEvalTerm (PresburgerTerm con coeffs) = if all (\n -> n == 0) (Map.elems coeffs) then pure con else Nothing
    tryEvalFormula :: MyPresburgerFormula -> Maybe MyProp
    tryEvalFormula (ValF b) = pure b
    tryEvalFormula (EqnF t1 t2) = pure (==) <*> tryEvalTerm t1 <*> tryEvalTerm t2
    tryEvalFormula (LtnF t1 t2) = pure (<) <*> tryEvalTerm t1 <*> tryEvalTerm t2
    tryEvalFormula (LeqF t1 t2) = pure (<=) <*> tryEvalTerm t1 <*> tryEvalTerm t2
    tryEvalFormula (GtnF t1 t2) = pure (>) <*> tryEvalTerm t1 <*> tryEvalTerm t2
    tryEvalFormula (ModF t1 r t2) = pure areCongruentModulo <*> tryEvalTerm t1 <*> pure r <*> tryEvalTerm t2
    tryEvalFormula (NegF f1) = pure not <*> tryEvalFormula f1
    tryEvalFormula (DisF f1 f2) = pure (||) <*> tryEvalFormula f1 <*> tryEvalFormula f2
    tryEvalFormula (ConF f1 f2) = pure (&&) <*> tryEvalFormula f1 <*> tryEvalFormula f2
    tryEvalFormula (ImpF f1 f2) = pure (<=) <*> tryEvalFormula f1 <*> tryEvalFormula f2
    tryEvalFormula (IffF f1 f2) = pure (==) <*> tryEvalFormula f1 <*> tryEvalFormula f2
    tryEvalFormula (AllF y f1) = tryEvalFormula f1
    tryEvalFormula (ExsF y f1) = tryEvalFormula f1

addFVs :: PresburgerTermRep -> Set.Set MyVar -> Set.Set MyVar
addFVs (IVar x) = Set.insert x
addFVs (Zero) = id
addFVs (Succ t1) = addFVs t1
addFVs (Plus t1 t2) = addFVs t1 . addFVs t2

getFVs :: MyPresburgerFormulaRep -> Set.Set MyVar
getFVs (ValF b) = Set.empty
getFVs (EqnF t1 t2) = addFVs t1 (addFVs t2 Set.empty)
getFVs (LtnF t1 t2) = addFVs t1 (addFVs t2 Set.empty)
getFVs (LeqF t1 t2) = addFVs t1 (addFVs t2 Set.empty)
getFVs (GtnF t1 t2) = addFVs t1 (addFVs t2 Set.empty)
getFVs (ModF t1 r t2) = addFVs t1 (addFVs t2 Set.empty)
getFVs (NegF f1) = getFVs f1
getFVs (DisF f1 f2) = getFVs f1 `Set.union` getFVs f2
getFVs (ConF f1 f2) = getFVs f1 `Set.union` getFVs f2
getFVs (ImpF f1 f2) = getFVs f1 `Set.union` getFVs f2
getFVs (IffF f1 f2) = getFVs f1 `Set.union` getFVs f2
getFVs (AllF y f1) = y `Set.delete` getFVs f1
getFVs (ExsF y f1) = y `Set.delete` getFVs f1

chi :: MyPresburgerFormulaRep -> (MyVar -> PresburgerTermRep) -> MyVar
chi f sigma = succ (getMaxVarOf [ getMaxVarOf (addFVs (sigma x) Set.empty) | x <- Set.toAscList (getFVs f) ]) where
    getMaxVarOf :: Foldable container_of => container_of MyVar -> MyVar
    getMaxVarOf = flip (foldr (\z1 -> \acc -> \z2 -> callWithStrictArg acc (max z1 z2)) id) theMinNumOfMyVar

nilSubst :: (MyVar -> PresburgerTermRep)
nilSubst z = IVar z

consSubst :: (MyVar, PresburgerTermRep) -> (MyVar -> PresburgerTermRep) -> (MyVar -> PresburgerTermRep)
consSubst (x, t) sigma z = if x == z then t else sigma z

runTermSubst :: [(MyVar, PresburgerTermRep)] -> PresburgerTermRep -> PresburgerTermRep
runTermSubst = flip applySubstToTermRep . foldr consSubst nilSubst where
    applySubstToTermRep :: PresburgerTermRep -> (MyVar -> PresburgerTermRep) -> PresburgerTermRep
    applySubstToTermRep (IVar x) = flip callWithStrictArg x
    applySubstToTermRep (Zero) = pure Zero
    applySubstToTermRep (Succ t1) = pure Succ <*> applySubstToTermRep t1
    applySubstToTermRep (Plus t1 t2) = pure Plus <*> applySubstToTermRep t1 <*> applySubstToTermRep t2

runFormulaSubst :: [(MyVar, PresburgerTermRep)] -> MyPresburgerFormulaRep -> MyPresburgerFormulaRep
runFormulaSubst = flip applySubstToFormulaRep . foldr consSubst nilSubst where
    applySubstToTermRep :: PresburgerTermRep -> (MyVar -> PresburgerTermRep) -> PresburgerTermRep
    applySubstToTermRep (IVar x) = flip callWithStrictArg x
    applySubstToTermRep (Zero) = pure Zero
    applySubstToTermRep (Succ t1) = pure Succ <*> applySubstToTermRep t1
    applySubstToTermRep (Plus t1 t2) = pure Plus <*> applySubstToTermRep t1 <*> applySubstToTermRep t2
    applySubstToFormulaRep :: MyPresburgerFormulaRep -> (MyVar -> PresburgerTermRep) -> MyPresburgerFormulaRep
    applySubstToFormulaRep (ValF b) = pure ValF <*> pure b
    applySubstToFormulaRep (EqnF t1 t2) = pure EqnF <*> applySubstToTermRep t1 <*> applySubstToTermRep t2
    applySubstToFormulaRep (LtnF t1 t2) = pure LtnF <*> applySubstToTermRep t1 <*> applySubstToTermRep t2
    applySubstToFormulaRep (LeqF t1 t2) = pure LeqF <*> applySubstToTermRep t1 <*> applySubstToTermRep t2
    applySubstToFormulaRep (GtnF t1 t2) = pure GtnF <*> applySubstToTermRep t1 <*> applySubstToTermRep t2
    applySubstToFormulaRep (ModF t1 r t2) = pure ModF <*> applySubstToTermRep t1 <*> pure r <*> applySubstToTermRep t2
    applySubstToFormulaRep (NegF f1) = pure NegF <*> applySubstToFormulaRep f1
    applySubstToFormulaRep (DisF f1 f2) = pure DisF <*> applySubstToFormulaRep f1 <*> applySubstToFormulaRep f2
    applySubstToFormulaRep (ConF f1 f2) = pure ConF <*> applySubstToFormulaRep f1 <*> applySubstToFormulaRep f2
    applySubstToFormulaRep (ImpF f1 f2) = pure ImpF <*> applySubstToFormulaRep f1 <*> applySubstToFormulaRep f2
    applySubstToFormulaRep (IffF f1 f2) = pure IffF <*> applySubstToFormulaRep f1 <*> applySubstToFormulaRep f2
    applySubstToFormulaRep f = applySubstToQuantifier f <*> chi f
    applySubstToQuantifier :: MyPresburgerFormulaRep -> (MyVar -> PresburgerTermRep) -> MyVar -> MyPresburgerFormulaRep
    applySubstToQuantifier (AllF y f1) sigma z = AllF z (applySubstToFormulaRep f1 (consSubst (y, IVar z) sigma))
    applySubstToQuantifier (ExsF y f1) sigma z = ExsF z (applySubstToFormulaRep f1 (consSubst (y, IVar z) sigma))

toFormulaRep :: MyPresburgerFormula -> ErrMsgM MyPresburgerFormulaRep
toFormulaRep = pure addErrMsg <*> mkErrMsg <*> discompileFormula where
    mkErrMsg :: MyPresburgerFormula -> String
    mkErrMsg f = "The formula ``" ++ shows f "\'\' is ill-formed..."
    discompileTerm :: PresburgerTerm -> Maybe PresburgerTermRep
    discompileTerm (PresburgerTerm con coeffs) = pure (List.foldl' mkPlus) <*> (if con >= 0 then pure (recNat mkZero (const mkSucc) con) else Nothing) <*> (traverse (uncurry $ \var -> \coeff -> if var >= theMinNumOfMyVar && coeff > 0 then pure (recNat (mkIVar var) (const (flip mkPlus (mkIVar var))) (coeff - 1)) else Nothing) (Map.toAscList coeffs))
    discompileFormula :: MyPresburgerFormula -> Maybe MyPresburgerFormulaRep
    discompileFormula (ValF b) = pure mkValF <*> pure b
    discompileFormula (EqnF t1 t2) = pure mkEqnF <*> discompileTerm t1 <*> discompileTerm t2
    discompileFormula (LtnF t1 t2) = pure mkLtnF <*> discompileTerm t1 <*> discompileTerm t2
    discompileFormula (LeqF t1 t2) = pure mkLeqF <*> discompileTerm t1 <*> discompileTerm t2
    discompileFormula (GtnF t1 t2) = pure mkGtnF <*> discompileTerm t1 <*> discompileTerm t2
    discompileFormula (ModF t1 r t2) = pure mkModF <*> discompileTerm t1 <*> (if r > 0 then pure r else Nothing) <*> discompileTerm t2
    discompileFormula (NegF f1) = pure mkNegF <*> discompileFormula f1
    discompileFormula (DisF f1 f2) = pure mkDisF <*> discompileFormula f1 <*> discompileFormula f2
    discompileFormula (ConF f1 f2) = pure mkConF <*> discompileFormula f1 <*> discompileFormula f2
    discompileFormula (ImpF f1 f2) = pure mkImpF <*> discompileFormula f1 <*> discompileFormula f2
    discompileFormula (IffF f1 f2) = pure mkIffF <*> discompileFormula f1 <*> discompileFormula f2
    discompileFormula (AllF y f1) = pure mkAllF <*> (if y >= theMinNumOfMyVar then pure y else Nothing) <*> discompileFormula f1
    discompileFormula (ExsF y f1) = pure mkExsF <*> (if y >= theMinNumOfMyVar then pure y else Nothing) <*> discompileFormula f1
    mkIVar :: MyVar -> PresburgerTermRep
    mkIVar x = IVar x
    mkZero :: PresburgerTermRep
    mkZero = Zero
    mkSucc :: PresburgerTermRep -> PresburgerTermRep
    mkSucc t1 = t1 `seq` Succ t1
    mkPlus :: PresburgerTermRep -> PresburgerTermRep -> PresburgerTermRep
    mkPlus t1 t2 = t1 `seq` t2 `seq` Plus t1 t2
    mkValF :: MyProp -> MyPresburgerFormulaRep
    mkValF b = b `seq` ValF b
    mkEqnF :: PresburgerTermRep -> PresburgerTermRep -> MyPresburgerFormulaRep
    mkEqnF t1 t2 = t1 `seq` t2 `seq` EqnF t1 t2
    mkLtnF :: PresburgerTermRep -> PresburgerTermRep -> MyPresburgerFormulaRep
    mkLtnF t1 t2 = t1 `seq` t2 `seq` LtnF t1 t2
    mkLeqF :: PresburgerTermRep -> PresburgerTermRep -> MyPresburgerFormulaRep
    mkLeqF t1 t2 = t1 `seq` t2 `seq` LeqF t1 t2
    mkGtnF :: PresburgerTermRep -> PresburgerTermRep -> MyPresburgerFormulaRep
    mkGtnF t1 t2 = t1 `seq` t2 `seq` GtnF t1 t2
    mkModF :: PresburgerTermRep -> PositiveInteger -> PresburgerTermRep -> MyPresburgerFormulaRep
    mkModF t1 r t2 = t1 `seq` t2 `seq` ModF t1 r t2
    mkNegF :: MyPresburgerFormulaRep -> MyPresburgerFormulaRep
    mkNegF f1 = f1 `seq` NegF f1
    mkConF :: MyPresburgerFormulaRep -> MyPresburgerFormulaRep -> MyPresburgerFormulaRep
    mkConF f1 f2 = f1 `seq` f2 `seq` ConF f1 f2
    mkDisF :: MyPresburgerFormulaRep -> MyPresburgerFormulaRep -> MyPresburgerFormulaRep
    mkDisF f1 f2 = f1 `seq` f2 `seq` DisF f1 f2
    mkImpF :: MyPresburgerFormulaRep -> MyPresburgerFormulaRep -> MyPresburgerFormulaRep
    mkImpF f1 f2 = f1 `seq` f2 `seq` ImpF f1 f2
    mkIffF :: MyPresburgerFormulaRep -> MyPresburgerFormulaRep -> MyPresburgerFormulaRep
    mkIffF f1 f2 = f1 `seq` f2 `seq` IffF f1 f2
    mkAllF :: MyVar -> MyPresburgerFormulaRep -> MyPresburgerFormulaRep
    mkAllF y f1 = f1 `seq` AllF y f1
    mkExsF :: MyVar -> MyPresburgerFormulaRep -> MyPresburgerFormulaRep
    mkExsF y f1 = f1 `seq` ExsF y f1
