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

type MyProp = Bool

data PresburgerTerm
    = PresburgerTerm 
        { getConstantTerm :: !(MyNat)
        , getCoefficients :: !(Map.Map MyVar MyCoefficient)
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
    fmap z (ValF b) = ValF b
    fmap z (EqnF t1 t2) = EqnF (z t1) (z t2)
    fmap z (LtnF t1 t2) = LtnF (z t1) (z t2)
    fmap z (LeqF t1 t2) = LeqF (z t1) (z t2)
    fmap z (GtnF t1 t2) = GtnF (z t1) (z t2)
    fmap z (ModF t1 r t2) = ModF (z t1) r (z t2)
    fmap z (NegF f1) = NegF (fmap z f1)
    fmap z (DisF f1 f2) = DisF (fmap z f1) (fmap z f2)
    fmap z (ConF f1 f2) = ConF (fmap z f1) (fmap z f2)
    fmap z (ImpF f1 f2) = ImpF (fmap z f1) (fmap z f2)
    fmap z (IffF f1 f2) = IffF (fmap z f1) (fmap z f2)
    fmap z (AllF y f1) = AllF y (fmap z f1)
    fmap z (ExsF y f1) = ExsF y (fmap z f1)

theMinNumOfMyVar :: MyVar
theMinNumOfMyVar = 1

showsMyVar :: MyVar -> ShowS
showsMyVar x = if x >= theMinNumOfMyVar then strstr "v" . shows x else strstr "?v" . (if x > 0 then id else strstr "_") . shows (abs x)

areCongruentModulo :: MyNat -> PositiveInteger -> MyNat -> MyProp
areCongruentModulo n1 r n2 = if r > 0 then n1 `mod` r == n2 `mod` r else error "areCongruentModulo: r must be positive"

plusCoeff :: (MyVar, MyCoefficient) -> Map.Map MyVar MyCoefficient -> Map.Map MyVar MyCoefficient
plusCoeff (x, n) = Map.alter (maybe (callWithStrictArg Just n) (\n' -> callWithStrictArg Just (n + n'))) x

compilePresburgerTerm :: PresburgerTermRep -> PresburgerTerm
compilePresburgerTerm = go where
    go :: PresburgerTermRep -> PresburgerTerm
    go (IVar x) = mkIVar x
    go (Zero) = mkZero
    go (Succ t1) = mkSucc (go t1)
    go (Plus t1 t2) = mkPlus (go t1) (go t2)
    mkIVar :: MyVar -> PresburgerTerm
    mkIVar x = PresburgerTerm 0 (Map.singleton x 1)
    mkZero :: PresburgerTerm
    mkZero = PresburgerTerm 0 Map.empty
    mkSucc :: PresburgerTerm -> PresburgerTerm
    mkSucc (PresburgerTerm con1 coeffs1) = PresburgerTerm (succ con1) coeffs1
    mkPlus :: PresburgerTerm -> PresburgerTerm -> PresburgerTerm
    mkPlus (PresburgerTerm con1 coeffs1) (PresburgerTerm con2 coeffs2) = PresburgerTerm (con1 + con2) (foldr plusCoeff coeffs1 (Map.toAscList coeffs2))

eliminateQuantifierReferringToTheBookWrittenByPeterHinman :: MyPresburgerFormula -> MyPresburgerFormula
eliminateQuantifierReferringToTheBookWrittenByPeterHinman = asterify . simplify where
    orcat :: [MyPresburgerFormula] -> MyPresburgerFormula
    orcat = List.foldl' mkDisF (mkValF False)
    andcat :: [MyPresburgerFormula] -> MyPresburgerFormula
    andcat = foldr mkConF (mkValF True)
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
    eliminateExsF = curry step1 where
        step1 :: (MyVar, MyPresburgerFormula) -> MyPresburgerFormula
        step1 = fmap (orcat . uncurry callWithStrictArg) (map . step2 <^> makeDNF . eliminateNegF) where
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
        step2 :: MyVar -> [MyPresburgerFormula] -> MyPresburgerFormula
        step2 x = andcatKlasses . toKlasses where
            toKlasses :: [MyPresburgerFormula] -> [PresburgerKlass]
            toKlasses = map constructKlass where
                extractCoefficient :: PresburgerTerm -> (MyCoefficient, PresburgerTerm)
                extractCoefficient t = maybe (0, t) (\n -> (n, PresburgerTerm (getConstantTerm t) (Map.delete x (getCoefficients t)))) (Map.lookup x (getCoefficients t))
                constructKlass :: MyPresburgerFormula -> PresburgerKlass
                constructKlass (EqnF t1 t2) = forEqnF (extractCoefficient t1) (extractCoefficient t2)
                constructKlass (LtnF t1 t2) = forLtnF (extractCoefficient t1) (extractCoefficient t2)
                constructKlass (ModF t1 r t2) = forModF (extractCoefficient t1) r (extractCoefficient t2)
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
            andcatKlasses :: [PresburgerKlass] -> MyPresburgerFormula
            andcatKlasses my_klasses = if areOnlyEtcs then andcatEtcs else andcatKlasses' $! List.foldl' getLCM 1 theCoefficients where
                areOnlyEtcs :: Bool
                areOnlyEtcs = null theCoefficients
                theCoefficients :: [PositiveInteger]
                theCoefficients = do
                    klass <- my_klasses
                    case klass of
                        (KlassEqn m t1 t2) -> return m
                        (KlassLtn m t1 t2) -> return m
                        (KlassGtn m t1 t2) -> return m
                        (KlassMod m t1 r t2) -> return m
                        (KlassEtc f) -> []
                andcatEtcs :: MyPresburgerFormula
                andcatEtcs = andcat [ f | (KlassEtc f) <- my_klasses ]
                andcatKlasses' :: PositiveInteger -> MyPresburgerFormula
                andcatKlasses' theLCM = mkConF (step3 theCollectionOfProperKlasses) andcatEtcs where
                    theEqns :: [(PresburgerTerm, PresburgerTerm)]
                    theEqns = [ (multiply (theLCM `div` m) t1, multiply (theLCM `div` m) t2) | (KlassEqn m t1 t2) <- my_klasses ]
                    theLtns :: [(PresburgerTerm, PresburgerTerm)]
                    theLtns = [ (multiply (theLCM `div` m) t1, multiply (theLCM `div` m) t2) | (KlassLtn m t1 t2) <- my_klasses ]
                    theGtns :: [(PresburgerTerm, PresburgerTerm)]
                    theGtns = [ (multiply (theLCM `div` m) t1, multiply (theLCM `div` m) t2) | (KlassGtn m t1 t2) <- my_klasses ]
                    theMods :: [(PositiveInteger, (PresburgerTerm, PresburgerTerm))]
                    theMods = [ ((theLCM `div` m) * r, (multiply (theLCM `div` m) t1, multiply (theLCM `div` m) t2)) | (KlassMod m t1 r t2) <- my_klasses ]
                    theCollectionOfProperKlasses :: CollectionOfProperKlasses
                    theCollectionOfProperKlasses = CollectionOfProperKlasses
                        { _Eqns = theEqns
                        , _Ltns = theLtns
                        , _Gtns = (mkNum 1, mkNum 0) : theGtns
                        , _Mods = (theLCM, (mkNum 0, mkNum 0)) : theMods
                        , _TheR = List.foldl' getLCM theLCM (map fst theMods)
                        }
        step3 :: CollectionOfProperKlasses -> MyPresburgerFormula
        step3 (CollectionOfProperKlasses theEqns0 theLtns0 theGtns0 theMods0 theR)
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
                ((t, t') : theEqns') -> andcat
                    [ andcat [ mkEqnF (mkPlus t' t1) (mkPlus t2 t) | (t1, t2) <- theEqns' ]
                    , andcat [ mkLtnF (mkPlus t' t1) (mkPlus t2 t) | (t1, t2) <- theLtns0 ]
                    , andcat [ mkGtnF (mkPlus t' t1) (mkPlus t2 t) | (t1, t2) <- theGtns0 ]
                    , andcat [ mkModF (mkPlus t' t1) r (mkPlus t2 t) | (r, (t1, t2)) <- theMods0 ]
                    ]
    mkNum :: MyNat -> PresburgerTerm
    mkNum k = PresburgerTerm k Map.empty
    mkPlus :: PresburgerTerm -> PresburgerTerm -> PresburgerTerm
    mkPlus (PresburgerTerm con1 coeffs1) (PresburgerTerm con2 coeffs2) = PresburgerTerm (con1 + con2) (foldr plusCoeff coeffs1 (Map.toAscList coeffs2))
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
    mkModF t1 r t2 = if r > 0 then mkCongruence (modify t1) r (modify t2) else error "mkModF: r must be positive" where
        modify :: PresburgerTerm -> PresburgerTerm
        modify (PresburgerTerm con coeffs) = PresburgerTerm (con `mod` r) (Map.filter (\n -> not (n == 0)) (Map.map (\n -> n `mod` r) coeffs))
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
    mkCongruence :: PresburgerTerm -> PositiveInteger -> PresburgerTerm -> MyPresburgerFormula
    mkCongruence t1 r t2
        | r > 0 = if getCoefficients t1 == getCoefficients t2 then mkValF (areCongruentModulo (getConstantTerm t1) r (getConstantTerm t2)) else ModF t1 r t2
        | otherwise = error "mkCongruence: r must be positive"
    multiply :: MyNat -> PresburgerTerm -> PresburgerTerm
    multiply k t
        | k == 0 = mkNum 0
        | k == 1 = t
        | k >= 0 = PresburgerTerm (getConstantTerm t * k) (Map.map (\n -> n * k) (getCoefficients t))
        | otherwise = error "multiply: negative input"
    getLCM :: PositiveInteger -> PositiveInteger -> PositiveInteger
    getLCM k1 k2 = maybe ((k1 * k2) `div` (getGCD k1 k2)) id (lookup 1 [(k1, k2), (k2, k1)])
    trick :: MyPresburgerFormula -> (MyPresburgerFormula, MyPresburgerFormula) -> Maybe MyPresburgerFormula
    trick (ValF b) = if b then pure . fst else pure . snd
    trick _ = pure Nothing

addFVs :: PresburgerTermRep -> Set.Set MyVar -> Set.Set MyVar
addFVs (IVar x) = if x >= theMinNumOfMyVar then Set.insert x else id
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

convertFormulaToRep :: MyPresburgerFormula -> ErrMsgM MyPresburgerFormulaRep
convertFormulaToRep = pure addErrMsg <*> mkErrMsg <*> discompileFormula where
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
