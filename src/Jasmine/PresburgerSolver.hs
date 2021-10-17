module Jasmine.PresburgerSolver where

import qualified Data.List as List
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Y.Base
import Z.Algo.Function
import Z.Utils

type MyVar = PositiveInteger

type Coefficient = PositiveInteger

type PresburgerFormula = Formula PresburgerTerm

type PresburgerFormulaRep = Formula PresburgerTermRep

type MySubst = MyVar -> PresburgerTermRep

data PresburgerTermRep
    = IVar MyVar
    | Zero
    | Succ PresburgerTermRep
    | Plus PresburgerTermRep PresburgerTermRep
    deriving (Eq)

data PresburgerTerm
    = PresburgerTerm 
        { getConstantTerm :: MyNat
        , getCoefficients :: Map.Map MyVar Coefficient
        }
    deriving (Eq)

data Formula term
    = ValF Bool
    | EqnF term term
    | LtnF term term
    | LeqF term term
    | GtnF term term
    | ModF term PositiveInteger term
    | NegF (Formula term)
    | DisF (Formula term) (Formula term)
    | ConF (Formula term) (Formula term)
    | ImpF (Formula term) (Formula term)
    | IffF (Formula term) (Formula term)
    | AllF MyVar (Formula term)
    | ExsF MyVar (Formula term)
    deriving (Eq)

data PresburgerKlass
    = KlassEqn !Coefficient !PresburgerTerm !PresburgerTerm
    | KlassLtn !Coefficient !PresburgerTerm !PresburgerTerm
    | KlassGtn !Coefficient !PresburgerTerm !PresburgerTerm
    | KlassMod !Coefficient !PresburgerTerm !PositiveInteger !PresburgerTerm
    | KlassEtc !PresburgerFormula
    deriving (Eq)

instance Show PresburgerTermRep where
    showsPrec prec = dispatch where
        myPrecIs :: Precedence -> ShowS -> ShowS
        myPrecIs prec' ss = if prec > prec' then strstr "(" . ss . strstr ")" else ss
        dispatch :: PresburgerTermRep -> ShowS
        dispatch (IVar x) = myPrecIs 11 $ showsMyVar x
        dispatch (Zero) = myPrecIs 11 $ strstr "0"
        dispatch (Succ t1) = myPrecIs 11 $ strstr "S " . showsPrec 10 t1
        dispatch (Plus t1 t2) = myPrecIs 4 $ showsPrec 4 t1 . strstr " + " . showsPrec 5 t2

instance Show PresburgerTerm where
    showsPrec _ (PresburgerTerm con coeffs) = ppunc " + " (map showsMyVarWithCoefficient (Map.toAscList coeffs)) . (if Map.null coeffs then shows con else (if con == 0 then id else strstr " + " . shows con)) where
        showsMyVarWithCoefficient :: (MyVar, Coefficient) -> ShowS
        showsMyVarWithCoefficient (x, n) = if n == 1 then showsMyVar x else shows n . strstr " " . showsMyVar x

instance Functor Formula where
    fmap = mapTermInFormula

instance Show term => Show (Formula term) where
    showsPrec prec = dispatch where
        myPrecIs :: Precedence -> ShowS -> ShowS
        myPrecIs prec' ss = if prec > prec' then strstr "(" . ss . strstr ")" else ss
        dispatch :: Show term => Formula term -> ShowS
        dispatch (ValF b) = myPrecIs 11 $ strstr (if b then "~ _|_" else "_|_")
        dispatch (EqnF t1 t2) = myPrecIs 9 $ shows t1 . strstr " = " . shows t2
        dispatch (LtnF t1 t2) = myPrecIs 9 $ shows t1 . strstr " < " . shows t2
        dispatch (LeqF t1 t2) = myPrecIs 9 $ shows t1 . strstr " =< " . shows t2
        dispatch (GtnF t1 t2) = myPrecIs 9 $ shows t1 . strstr " > " . shows t2
        dispatch (ModF t1 r t2) = myPrecIs 9 $ shows t1 . strstr " ==_{" . shows r . strstr "} " . shows t2
        dispatch (NegF f1) = myPrecIs 8 $ strstr "~ " . showsPrec 9 f1
        dispatch (DisF f1 f2) = myPrecIs 6 $ showsPrec 6 f1 . strstr " \\/ " . showsPrec 7 f2
        dispatch (ConF f1 f2) = myPrecIs 7 $ showsPrec 7 f1 . strstr " /\\ " . showsPrec 8 f2
        dispatch (ImpF f1 f2) = myPrecIs 0 $ showsPrec 1 f1 . strstr " -> " . showsPrec 0 f2
        dispatch (IffF f1 f2) = myPrecIs 0 $ showsPrec 1 f1 . strstr " <-> " . showsPrec 1 f2
        dispatch (AllF y f1) = myPrecIs 8 $ strstr "forall " . showsMyVar y . strstr ", " . showsPrec 8 f1
        dispatch (ExsF y f1) = myPrecIs 8 $ strstr "exists " . showsMyVar y . strstr ", " . showsPrec 8 f1

showsMyVar :: MyVar -> ShowS
showsMyVar x = strstr "v" . shows x

compileTerm :: PresburgerTermRep -> PresburgerTerm
compileTerm = go where
    mkTerm :: MyNat -> Map.Map MyVar Coefficient -> PresburgerTerm
    mkTerm con coeffs = con `seq` coeffs `seq` PresburgerTerm con coeffs
    go :: PresburgerTermRep -> PresburgerTerm
    go (IVar x) = mkTerm 0 (Map.singleton x 1)
    go (Zero) = mkTerm 0 Map.empty
    go (Succ t1) = case go t1 of
        PresburgerTerm con1 coeffs1 -> mkTerm (succ con1) coeffs1
    go (Plus t1 t2) = case (go t1, go t2) of
        (PresburgerTerm con1 coeffs1, PresburgerTerm con2 coeffs2) -> mkTerm (con1 + con2) (foldr plusCoeff coeffs1 (Map.toAscList coeffs2))
    plusCoeff :: (MyVar, Coefficient) -> Map.Map MyVar Coefficient -> Map.Map MyVar Coefficient
    plusCoeff (x, n) = Map.alter (maybe (callWithStrictArg Just n) (\n' -> callWithStrictArg Just (n + n'))) x

eliminateQuantifier :: PresburgerFormula -> PresburgerFormula
eliminateQuantifier = eliminateOneByOne where
    multiplyTerm :: MyNat -> PresburgerTerm -> PresburgerTerm
    multiplyTerm k t
        | k == 0 = mkNum 0
        | k == 1 = t
        | k >= 0 = mkTerm (getConstantTerm t * k) (Map.map (\n -> n * k) (getCoefficients t))
        | otherwise = error "multiplyTerm: negative input"
    orcat :: [PresburgerFormula] -> PresburgerFormula
    orcat [] = mkBotF
    orcat (f : fs) = List.foldl' mkDisF f fs
    andcat :: [PresburgerFormula] -> PresburgerFormula
    andcat = foldr mkConF mkTopF
    getLCM :: MyNat -> MyNat -> MyNat
    getLCM x y = (x * y) `div` (getGCD x y)
    eliminateOneByOne :: PresburgerFormula -> PresburgerFormula
    eliminateOneByOne = asterify . simplify where
        simplify :: PresburgerFormula -> PresburgerFormula
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
        asterify :: PresburgerFormula -> PresburgerFormula
        asterify (NegF f1) = mkNegF (asterify f1)
        asterify (ConF f1 f2) = mkConF (asterify f1) (asterify f2)
        asterify (DisF f1 f2) = mkDisF (asterify f1) (asterify f2)
        asterify (ExsF y f1) = eliminateExsF y (asterify f1)
        asterify atom_f = atom_f
    eliminateExsF :: MyVar -> PresburgerFormula -> PresburgerFormula
    eliminateExsF = curry step1 where
        step1 :: (MyVar, PresburgerFormula) -> PresburgerFormula
        step1 = myMain where
            runNeg :: PresburgerFormula -> PresburgerFormula
            runNeg (ValF b) = mkValF (not b)
            runNeg (EqnF t1 t2) = mkDisF (mkLtnF t1 t2) (mkGtnF t1 t2)
            runNeg (LtnF t1 t2) = mkDisF (mkEqnF t1 t2) (mkGtnF t1 t2)
            runNeg (ModF t1 r t2) = orcat [ mkModF t1 r (mkPlus t2 (mkNum i)) | i <- [1 .. r - 1] ]
            runNeg (NegF f1) = f1
            runNeg (DisF f1 f2) = mkConF (runNeg f1) (runNeg f2)
            runNeg (ConF f1 f2) = mkDisF (runNeg f1) (runNeg f2)
            removeNegation :: PresburgerFormula -> PresburgerFormula
            removeNegation (NegF f1) = runNeg (removeNegation f1)
            removeNegation (DisF f1 f2) = mkDisF (removeNegation f1) (removeNegation f2)
            removeNegation (ConF f1 f2) = mkConF (removeNegation f1) (removeNegation f2)
            removeNegation atom_f = atom_f
            makeDNFfromNoNeg :: PresburgerFormula -> [[PresburgerFormula]]
            makeDNFfromNoNeg (DisF f1 f2) = makeDNFfromNoNeg f1 ++ makeDNFfromNoNeg f2
            makeDNFfromNoNeg (ConF f1 f2) = [ fs1 ++ fs2 | fs1 <- makeDNFfromNoNeg f1, fs2 <- makeDNFfromNoNeg f2 ]
            makeDNFfromNoNeg atom_f = [one atom_f]
            myMain :: (MyVar, PresburgerFormula) -> PresburgerFormula
            myMain (x, psi) = orcat [ step2 x conjs | conjs <- makeDNFfromNoNeg (removeNegation psi) ]
        step2 :: MyVar -> [PresburgerFormula] -> PresburgerFormula
        step2 x = myMain where
            mkKlasses :: [PresburgerFormula] -> [PresburgerKlass]
            mkKlasses = map mkKlass where
                extractCoefficient :: PresburgerTerm -> (MyNat, PresburgerTerm)
                extractCoefficient t = case Map.lookup x (getCoefficients t) of
                    Nothing -> (0, t)
                    Just n -> (n, mkTerm (getConstantTerm t) (Map.delete x (getCoefficients t)))
                mkKlass :: PresburgerFormula -> PresburgerKlass
                mkKlass (EqnF t1 t2) = case (extractCoefficient t1, extractCoefficient t2) of
                    ((m1, t1'), (m2, t2')) -> case m1 `compare` m2 of
                        LT -> KlassEqn (m2 - m1) t2' t1'
                        EQ -> KlassEtc (mkEqnF t1' t2')
                        GT -> KlassEqn (m1 - m2) t1' t2'
                mkKlass (LtnF t1 t2) = case (extractCoefficient t1, extractCoefficient t2) of
                    ((m1, t1'), (m2, t2')) -> case m1 `compare` m2 of
                        LT -> KlassGtn (m2 - m1) t2' t1'
                        EQ -> KlassEtc (mkLtnF t1' t2')
                        GT -> KlassLtn (m1 - m2) t1' t2'
                mkKlass (ModF t1 r t2) = case (extractCoefficient t1, extractCoefficient t2) of
                    ((m1, t1'), (m2, t2')) -> case m1 `compare` m2 of
                        LT -> KlassMod (m2 - m1) t2' r t1'
                        EQ -> KlassEtc (mkModF t1' r t2')
                        GT -> KlassMod (m1 - m2) t1' r t2'
                mkKlass f = KlassEtc f
            standardizeCoefficient :: [PresburgerKlass] -> Either [PresburgerKlass] (MyNat, [PresburgerKlass])
            standardizeCoefficient your_klasses = maybe (Left your_klasses) (Right . ((,) <*> theStandardizedKlasses)) theMaybeLCM where
                theMaybeLCM :: Maybe MyNat
                theMaybeLCM = calcLCM theCoefficients where
                    calcLCM :: [MyNat] -> Maybe MyNat
                    calcLCM [] = Nothing
                    calcLCM (m : ms) = callWithStrictArg return (List.foldl' getLCM m ms)
                    theCoefficients :: [MyNat]
                    theCoefficients = do
                        klass <- your_klasses
                        case klass of
                            KlassEqn m t1 t2 -> return m
                            KlassLtn m t1 t2 -> return m
                            KlassGtn m t1 t2 -> return m
                            KlassMod m t1 r t2 -> return m
                            KlassEtc f -> []
                theStandardizedKlasses :: MyNat -> [PresburgerKlass]
                theStandardizedKlasses theLCM = map myLoop your_klasses where
                    myLoop :: PresburgerKlass -> PresburgerKlass
                    myLoop (KlassEqn m t1 t2) = KlassEqn theLCM (multiplyTerm (theLCM `div` m) t1) (multiplyTerm (theLCM `div` m) t2)
                    myLoop (KlassLtn m t1 t2) = KlassLtn theLCM (multiplyTerm (theLCM `div` m) t1) (multiplyTerm (theLCM `div` m) t2)
                    myLoop (KlassGtn m t1 t2) = KlassGtn theLCM (multiplyTerm (theLCM `div` m) t1) (multiplyTerm (theLCM `div` m) t2)
                    myLoop (KlassMod m t1 r t2) = KlassMod theLCM (multiplyTerm (theLCM `div` m) t1) (r * (theLCM `div` m)) (multiplyTerm (theLCM `div` m) t2)
                    myLoop (KlassEtc f) = KlassEtc f
            myMain :: [PresburgerFormula] -> PresburgerFormula
            myMain conjs = case standardizeCoefficient (mkKlasses conjs) of
                Left my_klasses -> andcat [ f | KlassEtc f <- my_klasses ]
                Right (m, my_klasses) -> mkConF (andcat [ f | KlassEtc f <- my_klasses ]) (step3 [ (t1, t2) | KlassEqn _ t1 t2 <- my_klasses ] [ (t1, t2) | KlassLtn _ t1 t2 <- my_klasses ] ((mkNum 1, mkNum 0) : [ (t1, t2) | KlassGtn _ t1 t2 <- my_klasses ]) ((m, (mkNum 0, mkNum 0)) : [ (r, (t1, t2)) | KlassMod _ t1 r t2 <- my_klasses ]))
        step3 :: [(PresburgerTerm, PresburgerTerm)] -> [(PresburgerTerm, PresburgerTerm)] -> [(PresburgerTerm, PresburgerTerm)] -> [(PositiveInteger, (PresburgerTerm, PresburgerTerm))] -> PresburgerFormula
        step3 theEqns0 theLtns0 theGtns0 theMods0
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
                            | s <- [1 .. _R]
                            ]
                        ]
                    | (u, u') <- theLtns0
                    , (v', v) <- theGtns0
                    ]
                (t, t') : theEqns' -> andcat
                    [ andcat [ mkEqnF (mkPlus t' t1) (mkPlus t2 t) | (t1, t2) <- theEqns' ]
                    , andcat [ mkLtnF (mkPlus t' t1) (mkPlus t2 t) | (t1, t2) <- theLtns0 ]
                    , andcat [ mkGtnF (mkPlus t' t1) (mkPlus t2 t) | (t1, t2) <- theGtns0 ]
                    , andcat [ mkModF (mkPlus t' t1) r (mkPlus t2 t) | (r, (t1, t2)) <- theMods0 ]
                    ]
            where
                _R :: MyNat
                _R = List.foldl' getLCM 1 (map fst theMods0)
    mkTerm :: MyNat -> Map.Map MyVar Coefficient -> PresburgerTerm
    mkTerm con coeffs = con `seq` coeffs `seq` PresburgerTerm con coeffs
    mkNum :: MyNat -> PresburgerTerm
    mkNum n = mkTerm n Map.empty
    mkPlus :: PresburgerTerm -> PresburgerTerm -> PresburgerTerm
    mkPlus (PresburgerTerm con1 coeffs1) (PresburgerTerm con2 coeffs2) = mkTerm (con1 + con2) (foldr plusCoeff coeffs1 (Map.toAscList coeffs2)) where
        plusCoeff :: (MyVar, Coefficient) -> Map.Map MyVar Coefficient -> Map.Map MyVar Coefficient
        plusCoeff (x, n) = Map.alter (maybe (callWithStrictArg Just n) (\n' -> callWithStrictArg Just (n + n'))) x
    mkValF :: Bool -> PresburgerFormula
    mkValF b = b `seq` ValF b
    mkEqnF :: PresburgerTerm -> PresburgerTerm -> PresburgerFormula
    mkEqnF t1 t2 = if t1 == t2 then mkTopF else t1 `seq` t2 `seq` EqnF t1 t2
    mkLtnF :: PresburgerTerm -> PresburgerTerm -> PresburgerFormula
    mkLtnF t1 t2
        | getCoefficients t1 == getCoefficients t2 = mkValF (getConstantTerm t1 < getConstantTerm t2)
        | otherwise = t1 `seq` t2 `seq` LtnF t1 t2
    mkModF :: PresburgerTerm -> PositiveInteger -> PresburgerTerm -> PresburgerFormula
    mkModF t1 r t2
        | r > 0 = case (reduceTermWithMod r t1, reduceTermWithMod r t2) of
            (t1', t2') -> if t1' == t2' then mkTopF else ModF t1' r t2'
        | otherwise = error "mkModF: r must be positive"
    mkLeqF :: PresburgerTerm -> PresburgerTerm -> PresburgerFormula
    mkLeqF t1 t2 = mkDisF (mkEqnF t1 t2) (mkLtnF t1 t2)
    mkGtnF :: PresburgerTerm -> PresburgerTerm -> PresburgerFormula
    mkGtnF t1 t2 = mkLtnF t2 t1
    mkTopF :: PresburgerFormula
    mkTopF = mkValF True
    mkBotF :: PresburgerFormula
    mkBotF = mkValF False
    mkNegF :: PresburgerFormula -> PresburgerFormula
    mkNegF (ValF b) = mkValF (not b)
    mkNegF (NegF f1) = f1
    mkNegF f1 = NegF f1
    mkDisF :: PresburgerFormula -> PresburgerFormula -> PresburgerFormula
    mkDisF (ValF b) f2 = if b then mkTopF else f2
    mkDisF f1 (ValF b2) = if b2 then mkTopF else f1
    mkDisF f1 f2 = DisF f1 f2
    mkConF :: PresburgerFormula -> PresburgerFormula -> PresburgerFormula
    mkConF (ValF b) f2 = if b then f2 else mkBotF
    mkConF f1 (ValF b2) = if b2 then f1 else mkBotF
    mkConF f1 f2 = ConF f1 f2
    mkImpF :: PresburgerFormula -> PresburgerFormula -> PresburgerFormula
    mkImpF f1 f2 = mkDisF (mkNegF f1) f2
    mkIffF :: PresburgerFormula -> PresburgerFormula -> PresburgerFormula
    mkIffF f1 f2 = mkConF (mkImpF f1 f2) (mkImpF f2 f1)
    mkAllF :: MyVar -> PresburgerFormula -> PresburgerFormula
    mkAllF y f1 = mkNegF (mkExsF y (mkNegF f1))
    mkExsF :: MyVar -> PresburgerFormula -> PresburgerFormula
    mkExsF y f1 = f1 `seq` ExsF y f1
    reduceTermWithMod :: PositiveInteger -> PresburgerTerm -> PresburgerTerm
    reduceTermWithMod r (PresburgerTerm con coeffs) = if r > 0 then mkTerm (con `mod` r) (Map.fromAscList [ (x, n `mod` r) | (x, n) <- Map.toAscList coeffs, n `mod` r /= 0 ]) else error "reduceTermWithMod: negative input"

destiny :: PresburgerFormula -> Maybe Bool
destiny = tryEvalFormula where
    tryEvalTerm :: PresburgerTerm -> Maybe MyNat
    tryEvalTerm (PresburgerTerm con coeffs) = if Map.null coeffs then pure con else Nothing
    runEqn :: MyNat -> MyNat -> Bool
    runEqn n1 n2 = n1 == n2
    runLtn :: MyNat -> MyNat -> Bool
    runLtn n1 n2 = n1 < n2
    runLeq :: MyNat -> MyNat -> Bool
    runLeq n1 n2 = n1 <= n2
    runGtn :: MyNat -> MyNat -> Bool
    runGtn n1 n2 = n1 > n2
    runMod :: MyNat -> MyNat -> MyNat -> Bool
    runMod n1 r n2 = n1 `mod` r == n2 `mod` r
    runNeg :: Bool -> Bool
    runNeg = not
    runDis :: Bool -> Bool -> Bool
    runDis = (||)
    runCon :: Bool -> Bool -> Bool
    runCon = (&&)
    runImp :: Bool -> Bool -> Bool
    runImp = (<=)
    runIff :: Bool -> Bool -> Bool
    runIff = (==)
    tryEvalFormula :: PresburgerFormula -> Maybe Bool
    tryEvalFormula (ValF b) = pure b
    tryEvalFormula (EqnF t1 t2) = pure runEqn <*> tryEvalTerm t1 <*> tryEvalTerm t2
    tryEvalFormula (LtnF t1 t2) = pure runLtn <*> tryEvalTerm t1 <*> tryEvalTerm t2
    tryEvalFormula (LeqF t1 t2) = pure runLeq <*> tryEvalTerm t1 <*> tryEvalTerm t2
    tryEvalFormula (GtnF t1 t2) = pure runGtn <*> tryEvalTerm t1 <*> tryEvalTerm t2
    tryEvalFormula (ModF t1 r t2) = pure runMod <*> tryEvalTerm t1 <*> pure r <*> tryEvalTerm t2
    tryEvalFormula (NegF f1) = pure runNeg <*> tryEvalFormula f1
    tryEvalFormula (DisF f1 f2) = pure runDis <*> tryEvalFormula f1 <*> tryEvalFormula f2
    tryEvalFormula (ConF f1 f2) = pure runCon <*> tryEvalFormula f1 <*> tryEvalFormula f2
    tryEvalFormula (ImpF f1 f2) = pure runImp <*> tryEvalFormula f1 <*> tryEvalFormula f2
    tryEvalFormula (IffF f1 f2) = pure runIff <*> tryEvalFormula f1 <*> tryEvalFormula f2
    tryEvalFormula _ = Nothing

addFVs :: PresburgerTermRep -> Set.Set MyVar -> Set.Set MyVar
addFVs (IVar x) = Set.insert x
addFVs (Zero) = id
addFVs (Succ t1) = addFVs t1
addFVs (Plus t1 t2) = addFVs t1 . addFVs t2

getFVs :: PresburgerFormulaRep -> Set.Set MyVar
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

chi :: PresburgerFormulaRep -> MySubst -> MyVar
chi f sigma = succ (getMaxVarOf [ getMaxVarOf (addFVs (applyMySubstToVar x sigma) Set.empty) | x <- Set.toAscList (getFVs f) ]) where
    getMaxVarOf :: Foldable f => f MyVar -> MyVar
    getMaxVarOf = foldr max 0

getNewFV :: PresburgerFormulaRep -> MyVar
getNewFV f = chi f nilMySubst

nilMySubst :: MySubst
nilMySubst z = IVar z

consMySubst :: (MyVar, PresburgerTermRep) -> MySubst -> MySubst
consMySubst (x, t) sigma z = if x == z then t else applyMySubstToVar z sigma

makeMySubst :: [(MyVar, PresburgerTermRep)] -> MySubst
makeMySubst = foldr consMySubst nilMySubst

applyMySubstToVar :: MyVar -> MySubst -> PresburgerTermRep
applyMySubstToVar x sigma = sigma x

applyMySubstToTermRep :: PresburgerTermRep -> MySubst -> PresburgerTermRep
applyMySubstToTermRep (IVar x) = applyMySubstToVar x
applyMySubstToTermRep (Zero) = pure Zero
applyMySubstToTermRep (Succ t1) = pure Succ <*> applyMySubstToTermRep t1
applyMySubstToTermRep (Plus t1 t2) = pure Plus <*> applyMySubstToTermRep t1 <*> applyMySubstToTermRep t2

runMySubst :: MySubst -> PresburgerFormulaRep -> PresburgerFormulaRep
runMySubst = flip applyMySubstToFormulaRep where
    applyMySubstToFormulaRep :: PresburgerFormulaRep -> MySubst -> PresburgerFormulaRep
    applyMySubstToFormulaRep (ValF b) = pure (ValF b)
    applyMySubstToFormulaRep (EqnF t1 t2) = pure EqnF <*> applyMySubstToTermRep t1 <*> applyMySubstToTermRep t2
    applyMySubstToFormulaRep (LtnF t1 t2) = pure LtnF <*> applyMySubstToTermRep t1 <*> applyMySubstToTermRep t2
    applyMySubstToFormulaRep (LeqF t1 t2) = pure LeqF <*> applyMySubstToTermRep t1 <*> applyMySubstToTermRep t2
    applyMySubstToFormulaRep (GtnF t1 t2) = pure GtnF <*> applyMySubstToTermRep t1 <*> applyMySubstToTermRep t2
    applyMySubstToFormulaRep (ModF t1 r t2) = pure ModF <*> applyMySubstToTermRep t1 <*> pure r <*> applyMySubstToTermRep t2
    applyMySubstToFormulaRep (NegF f1) = pure NegF <*> applyMySubstToFormulaRep f1
    applyMySubstToFormulaRep (DisF f1 f2) = pure DisF <*> applyMySubstToFormulaRep f1 <*> applyMySubstToFormulaRep f2
    applyMySubstToFormulaRep (ConF f1 f2) = pure ConF <*> applyMySubstToFormulaRep f1 <*> applyMySubstToFormulaRep f2
    applyMySubstToFormulaRep (ImpF f1 f2) = pure ImpF <*> applyMySubstToFormulaRep f1 <*> applyMySubstToFormulaRep f2
    applyMySubstToFormulaRep (IffF f1 f2) = pure IffF <*> applyMySubstToFormulaRep f1 <*> applyMySubstToFormulaRep f2
    applyMySubstToFormulaRep f = applyMySubstToQuantifier f <*> chi f
    applyMySubstToQuantifier :: PresburgerFormulaRep -> MySubst -> MyVar -> PresburgerFormulaRep
    applyMySubstToQuantifier (AllF y f1) sigma z = AllF z (applyMySubstToFormulaRep f1 (consMySubst (y, IVar z) sigma))
    applyMySubstToQuantifier (ExsF y f1) sigma z = ExsF z (applyMySubstToFormulaRep f1 (consMySubst (y, IVar z) sigma))

mapTermInFormula :: (old_term -> term) -> Formula old_term -> Formula term
mapTermInFormula = go where
    mkValF :: Bool -> Formula term
    mkValF b = ValF b
    mkEqnF :: term -> term -> Formula term
    mkEqnF t1 t2 = t1 `seq` t2 `seq` EqnF t1 t2
    mkLtnF :: term -> term -> Formula term
    mkLtnF t1 t2 = t1 `seq` t2 `seq` LtnF t1 t2
    mkLeqF :: term -> term -> Formula term
    mkLeqF t1 t2 = t1 `seq` t2 `seq` LeqF t1 t2
    mkGtnF :: term -> term -> Formula term
    mkGtnF t1 t2 = t1 `seq` t2 `seq` GtnF t1 t2
    mkModF :: term -> PositiveInteger -> term -> Formula term
    mkModF t1 r t2 = t1 `seq` t2 `seq` ModF t1 r t2
    mkNegF :: Formula term -> Formula term
    mkNegF f1 = f1 `seq` NegF f1
    mkDisF :: Formula term -> Formula term -> Formula term
    mkDisF f1 f2 = f1 `seq` f2 `seq` DisF f1 f2
    mkConF :: Formula term -> Formula term -> Formula term
    mkConF f1 f2 = f1 `seq` f2 `seq` ConF f1 f2
    mkImpF :: Formula term -> Formula term -> Formula term
    mkImpF f1 f2 = f1 `seq` f2 `seq` ImpF f1 f2
    mkIffF :: Formula term -> Formula term -> Formula term
    mkIffF f1 f2 = f1 `seq` f2 `seq` IffF f1 f2
    mkAllF :: MyVar -> Formula term -> Formula term
    mkAllF y f1 = f1 `seq` AllF y f1
    mkExsF :: MyVar -> Formula term -> Formula term
    mkExsF y f1 = f1 `seq` ExsF y f1
    go :: (old_term -> term) -> Formula old_term -> Formula term
    go z (ValF b) = mkValF b
    go z (EqnF t1 t2) = mkEqnF (z t1) (z t2)
    go z (LtnF t1 t2) = mkLtnF (z t1) (z t2)
    go z (LeqF t1 t2) = mkLeqF (z t1) (z t2)
    go z (GtnF t1 t2) = mkGtnF (z t1) (z t2)
    go z (ModF t1 r t2) = mkModF (z t1) r (z t2)
    go z (NegF f1) = mkNegF (go z f1)
    go z (DisF f1 f2) = mkDisF (go z f1) (go z f2)
    go z (ConF f1 f2) = mkConF (go z f1) (go z f2)
    go z (ImpF f1 f2) = mkImpF (go z f1) (go z f2)
    go z (IffF f1 f2) = mkIffF (go z f1) (go z f2)
    go z (AllF y f1) = mkAllF y (go z f1)
    go z (ExsF y f1) = mkExsF y (go z f1)
