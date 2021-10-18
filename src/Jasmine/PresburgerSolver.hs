module Jasmine.PresburgerSolver where

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

type MySubst = MyVar -> PresburgerTermRep

type MyProp = Bool

data PresburgerTerm
    = PresburgerTerm 
        { getConstantTerm :: !MyNat
        , getCoefficients :: !(Map.Map MyVar MyCoefficient)
        }
    deriving (Eq)

data PresburgerFormula term
    = ValF MyProp
    | EqnF term term
    | LtnF term term
    | LeqF term term
    | GtnF term term
    | ModF term PositiveInteger term
    | NegF (PresburgerFormula term)
    | DisF (PresburgerFormula term) (PresburgerFormula term)
    | ConF (PresburgerFormula term) (PresburgerFormula term)
    | ImpF (PresburgerFormula term) (PresburgerFormula term)
    | IffF (PresburgerFormula term) (PresburgerFormula term)
    | AllF MyVar (PresburgerFormula term)
    | ExsF MyVar (PresburgerFormula term)
    deriving (Eq)

data PresburgerKlass
    = KlassEqn !MyCoefficient !PresburgerTerm !PresburgerTerm
    | KlassLtn !MyCoefficient !PresburgerTerm !PresburgerTerm
    | KlassGtn !MyCoefficient !PresburgerTerm !PresburgerTerm
    | KlassMod !MyCoefficient !PresburgerTerm !PositiveInteger !PresburgerTerm
    | KlassEtc !MyPresburgerFormula
    deriving (Eq, Show)

data PresburgerTermRep
    = IVar MyVar
    | Zero
    | Succ PresburgerTermRep
    | Plus PresburgerTermRep PresburgerTermRep
    deriving (Eq)

instance Show PresburgerTerm where
    showsPrec 0 (PresburgerTerm con coeffs) = strcat
        [ ppunc " + "
            [ if n == 1
                then showsMyVar x
                else strcat
                    [ if n < 0 then strstr "(" . shows n . strstr ")" else shows n
                    , strstr " " . showsMyVar x
                    ]
            | (x, n) <- Map.toAscList coeffs
            ]
        , case con `compare` 0 of
            (LT) -> if Map.null coeffs then shows con else strstr " - " . shows (abs con)
            (EQ) -> if Map.null coeffs then shows con else id
            (GT) -> if Map.null coeffs then shows con else strstr " + " . shows (abs con)
        ]
    showsPrec prec t = if prec > 5 then strstr "(" . shows t . strstr ")" else shows t

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
        dispatch (ConF f1 f2) = myPrecIs 2 $ showsPrec 2 f1 . strstr " /\\ " . showsPrec 3 f2
        dispatch (ImpF f1 f2) = myPrecIs 0 $ showsPrec 1 f1 . strstr " -> " . showsPrec 0 f2
        dispatch (IffF f1 f2) = myPrecIs 0 $ showsPrec 1 f1 . strstr " <-> " . showsPrec 1 f2
        dispatch (AllF y f1) = myPrecIs 3 $ strstr "forall " . showsMyVar y . strstr ", " . showsPrec 3 f1
        dispatch (ExsF y f1) = myPrecIs 3 $ strstr "exists " . showsMyVar y . strstr ", " . showsPrec 3 f1

instance Show PresburgerTermRep where
    showsPrec prec = dispatch where
        myPrecIs :: Precedence -> ShowS -> ShowS
        myPrecIs prec' ss = if prec > prec' then strstr "(" . ss . strstr ")" else ss
        dispatch :: PresburgerTermRep -> ShowS
        dispatch (IVar x) = myPrecIs 11 $ showsMyVar x
        dispatch (Zero) = myPrecIs 11 $ strstr "0"
        dispatch (Succ t1) = myPrecIs 10 $ strstr "S " . showsPrec 11 t1
        dispatch (Plus t1 t2) = myPrecIs 6 $ showsPrec 6 t1 . strstr " + " . showsPrec 7 t2

instance Functor PresburgerFormula where
    fmap = mapTermInPresburgerFormula

showsMyVar :: MyVar -> ShowS
showsMyVar x = if x > 0 then strstr "v" . shows x else strstr "?" . shows (negate x)

congruenceModulo :: MyNat -> PositiveInteger -> MyNat -> MyProp
congruenceModulo n1 r n2 = if r > 0 then n1 `mod` r == n2 `mod` r else error "congruenceModulo: r must be positive"

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
    plusCoeff :: (MyVar, MyCoefficient) -> Map.Map MyVar MyCoefficient -> Map.Map MyVar MyCoefficient
    plusCoeff (x, n) = Map.alter (maybe (callWithStrictArg Just n) (\n' -> callWithStrictArg Just (n + n'))) x

eliminateQuantifierReferringToTheBookWrittenByPeterHinman :: MyPresburgerFormula -> MyPresburgerFormula
eliminateQuantifierReferringToTheBookWrittenByPeterHinman = eliminateQuantifier where
    orcat :: [MyPresburgerFormula] -> MyPresburgerFormula
    orcat fs = if null fs then mkBotF else List.foldl' mkDisF (head fs) (tail fs)
    andcat :: [MyPresburgerFormula] -> MyPresburgerFormula
    andcat = foldr mkConF mkTopF
    eliminateQuantifier :: MyPresburgerFormula -> MyPresburgerFormula
    eliminateQuantifier = asterify . simplify where
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
        asterify atom_f = atom_f
    eliminateExsF :: MyVar -> MyPresburgerFormula -> MyPresburgerFormula
    eliminateExsF = curry step1 where
        step1 :: (MyVar, MyPresburgerFormula) -> MyPresburgerFormula
        step1 = fmap orcat (map . step2 . fst <*> makeDNF . eliminateNegF . snd) where
            unNegation :: MyPresburgerFormula -> MyPresburgerFormula
            unNegation (ValF b) = mkValF (not b)
            unNegation (EqnF t1 t2) = mkDisF (mkLtnF t1 t2) (mkGtnF t1 t2)
            unNegation (LtnF t1 t2) = mkDisF (mkEqnF t1 t2) (mkGtnF t1 t2)
            unNegation (ModF t1 r t2) = orcat [ mkModF t1 r (mkPlus t2 (mkNum i)) | i <- [1 .. r - 1] ]
            unNegation (NegF f1) = f1
            unNegation (DisF f1 f2) = mkConF (unNegation f1) (unNegation f2)
            unNegation (ConF f1 f2) = mkDisF (unNegation f1) (unNegation f2)
            eliminateNegF :: MyPresburgerFormula -> MyPresburgerFormula
            eliminateNegF (NegF f1) = unNegation (eliminateNegF f1)
            eliminateNegF (DisF f1 f2) = mkDisF (eliminateNegF f1) (eliminateNegF f2)
            eliminateNegF (ConF f1 f2) = mkConF (eliminateNegF f1) (eliminateNegF f2)
            eliminateNegF atom_f = atom_f
            makeDNF :: MyPresburgerFormula -> [[MyPresburgerFormula]]
            makeDNF (DisF f1 f2) = makeDNF f1 ++ makeDNF f2
            makeDNF (ConF f1 f2) = pure (++) <*> makeDNF f1 <*> makeDNF f2
            makeDNF atom_f = [one atom_f]
        step2 :: MyVar -> [MyPresburgerFormula] -> MyPresburgerFormula
        step2 x = buildBigConF . standardizeCoefficient . mkKlasses where
            mkKlasses :: [MyPresburgerFormula] -> [PresburgerKlass]
            mkKlasses = map mkKlass where
                extractMyCoefficient :: PresburgerTerm -> (MyNat, PresburgerTerm)
                extractMyCoefficient t = maybe (0, t) (\n -> (n, PresburgerTerm (getConstantTerm t) (Map.delete x (getCoefficients t)))) (Map.lookup x (getCoefficients t))
                mkKlass :: MyPresburgerFormula -> PresburgerKlass
                mkKlass (EqnF t1 t2) = case (extractMyCoefficient t1, extractMyCoefficient t2) of
                    ((m1, t1'), (m2, t2')) -> case m1 `compare` m2 of
                        (LT) -> KlassEqn (m2 - m1) t2' t1'
                        (EQ) -> KlassEtc (mkEqnF t1' t2')
                        (GT) -> KlassEqn (m1 - m2) t1' t2'
                mkKlass (LtnF t1 t2) = case (extractMyCoefficient t1, extractMyCoefficient t2) of
                    ((m1, t1'), (m2, t2')) -> case m1 `compare` m2 of
                        (LT) -> KlassGtn (m2 - m1) t2' t1'
                        (EQ) -> KlassEtc (mkLtnF t1' t2')
                        (GT) -> KlassLtn (m1 - m2) t1' t2'
                mkKlass (ModF t1 r t2) = case (extractMyCoefficient t1, extractMyCoefficient t2) of
                    ((m1, t1'), (m2, t2')) -> case m1 `compare` m2 of
                        (LT) -> KlassMod (m2 - m1) t2' r t1'
                        (EQ) -> KlassEtc (mkModF t1' r t2')
                        (GT) -> KlassMod (m1 - m2) t1' r t2'
                mkKlass f = KlassEtc f
            standardizeCoefficient :: [PresburgerKlass] -> Either [PresburgerKlass] (MyNat, [PresburgerKlass])
            standardizeCoefficient my_klasses = maybe (Left my_klasses) (curry Right <*> theStandardizedKlasses) theMaybeLCM where
                theMaybeLCM :: Maybe MyNat
                theMaybeLCM = calcLCM theMyCoefficients where
                    calcLCM :: [MyNat] -> Maybe MyNat
                    calcLCM [] = Nothing
                    calcLCM (m : ms) = callWithStrictArg Just (List.foldl' getLCM m ms)
                    theMyCoefficients :: [MyNat]
                    theMyCoefficients = do
                        klass <- my_klasses
                        case klass of
                            (KlassEqn m t1 t2) -> return m
                            (KlassLtn m t1 t2) -> return m
                            (KlassGtn m t1 t2) -> return m
                            (KlassMod m t1 r t2) -> return m
                            (KlassEtc f) -> []
                theStandardizedKlasses :: MyNat -> [PresburgerKlass]
                theStandardizedKlasses theLCM = map myLoop my_klasses where
                    myLoop :: PresburgerKlass -> PresburgerKlass
                    myLoop (KlassEqn m t1 t2) = KlassEqn theLCM (multiply (theLCM `div` m) t1) (multiply (theLCM `div` m) t2)
                    myLoop (KlassLtn m t1 t2) = KlassLtn theLCM (multiply (theLCM `div` m) t1) (multiply (theLCM `div` m) t2)
                    myLoop (KlassGtn m t1 t2) = KlassGtn theLCM (multiply (theLCM `div` m) t1) (multiply (theLCM `div` m) t2)
                    myLoop (KlassMod m t1 r t2) = KlassMod theLCM (multiply (theLCM `div` m) t1) (r * (theLCM `div` m)) (multiply (theLCM `div` m) t2)
                    myLoop (KlassEtc f) = KlassEtc f
            buildBigConF :: Either [PresburgerKlass] (MyNat, [PresburgerKlass]) -> MyPresburgerFormula
            buildBigConF (Left my_klasses) = andcat [ f | (KlassEtc f) <- my_klasses ]
            buildBigConF (Right (m, my_klasses)) = mkConF (andcat [ f | (KlassEtc f) <- my_klasses ]) (step3 [ (t1, t2) | (KlassEqn _ t1 t2) <- my_klasses ] [ (t1, t2) | (KlassLtn _ t1 t2) <- my_klasses ] ((mkNum 1, mkNum 0) : [ (t1, t2) | (KlassGtn _ t1 t2) <- my_klasses ]) ((m, (mkNum 0, mkNum 0)) : [ (r, (t1, t2)) | (KlassMod _ t1 r t2) <- my_klasses ]))
        step3 :: [(PresburgerTerm, PresburgerTerm)] -> [(PresburgerTerm, PresburgerTerm)] -> [(PresburgerTerm, PresburgerTerm)] -> [(PositiveInteger, (PresburgerTerm, PresburgerTerm))] -> MyPresburgerFormula
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
                ((t, t') : theEqns') -> andcat
                    [ andcat [ mkEqnF (mkPlus t' t1) (mkPlus t2 t) | (t1, t2) <- theEqns' ]
                    , andcat [ mkLtnF (mkPlus t' t1) (mkPlus t2 t) | (t1, t2) <- theLtns0 ]
                    , andcat [ mkGtnF (mkPlus t' t1) (mkPlus t2 t) | (t1, t2) <- theGtns0 ]
                    , andcat [ mkModF (mkPlus t' t1) r (mkPlus t2 t) | (r, (t1, t2)) <- theMods0 ]
                    ]
            where
                _R :: MyNat
                _R = List.foldl' getLCM 1 (map fst theMods0)
    mkNum :: MyNat -> PresburgerTerm
    mkNum n = PresburgerTerm n Map.empty
    mkPlus :: PresburgerTerm -> PresburgerTerm -> PresburgerTerm
    mkPlus (PresburgerTerm con1 coeffs1) (PresburgerTerm con2 coeffs2) = PresburgerTerm (con1 + con2) (foldr plusCoeff coeffs1 (Map.toAscList coeffs2)) where
        plusCoeff :: (MyVar, MyCoefficient) -> Map.Map MyVar MyCoefficient -> Map.Map MyVar MyCoefficient
        plusCoeff (x, n) = Map.alter (maybe (callWithStrictArg Just n) (\n' -> callWithStrictArg Just (n + n'))) x
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
    mkModF t1 r t2 = if r > 0 then makeModF (reduceTermWithMod t1) r (reduceTermWithMod t2) else error "mkModF: r must be positive" where
        reduceTermWithMod :: PresburgerTerm -> PresburgerTerm
        reduceTermWithMod t = PresburgerTerm (getConstantTerm t `mod` r) (Map.fromAscList [ (x, n `mod` r) | (x, n) <- Map.toAscList (getCoefficients t), n `mod` r /= 0 ])
    mkNegF :: MyPresburgerFormula -> MyPresburgerFormula
    mkNegF (ValF b) = mkValF (not b)
    mkNegF (NegF f1) = f1
    mkNegF f1 = NegF f1
    mkDisF :: MyPresburgerFormula -> MyPresburgerFormula -> MyPresburgerFormula
    mkDisF (ValF b1) f2 = if b1 then mkTopF else f2
    mkDisF f1 (ValF b2) = if b2 then mkTopF else f1
    mkDisF f1 f2 = DisF f1 f2
    mkConF :: MyPresburgerFormula -> MyPresburgerFormula -> MyPresburgerFormula
    mkConF (ValF b1) f2 = if b1 then f2 else mkBotF
    mkConF f1 (ValF b2) = if b2 then f1 else mkBotF
    mkConF f1 f2 = ConF f1 f2
    mkImpF :: MyPresburgerFormula -> MyPresburgerFormula -> MyPresburgerFormula
    mkImpF f1 f2 = mkDisF (mkNegF f1) f2
    mkIffF :: MyPresburgerFormula -> MyPresburgerFormula -> MyPresburgerFormula
    mkIffF f1 f2 = mkConF (mkImpF f1 f2) (mkImpF f2 f1)
    mkAllF :: MyVar -> MyPresburgerFormula -> MyPresburgerFormula
    mkAllF y f1 = mkNegF (mkExsF y (mkNegF f1))
    mkExsF :: MyVar -> MyPresburgerFormula -> MyPresburgerFormula
    mkExsF y f1 = f1 `seq` ExsF y f1
    mkTopF :: MyPresburgerFormula
    mkTopF = mkValF True
    mkBotF :: MyPresburgerFormula
    mkBotF = mkValF False
    makeModF :: PresburgerTerm -> PositiveInteger -> PresburgerTerm -> MyPresburgerFormula
    makeModF t1 r t2 = if getCoefficients t1 == getCoefficients t2 then mkValF (congruenceModulo (getConstantTerm t1) r (getConstantTerm t2)) else ModF t1 r t2
    multiply :: MyNat -> PresburgerTerm -> PresburgerTerm
    multiply k t
        | k == 0 = mkNum 0
        | k == 1 = t
        | k >= 0 = PresburgerTerm (getConstantTerm t * k) (Map.map (\n -> n * k) (getCoefficients t))
        | otherwise = error "multiply: negative input"
    getLCM :: MyNat -> MyNat -> MyNat
    getLCM n1 n2 = (n1 * n2) `div` (getGCD n1 n2)

checkMyPresburgerFormulaIsTheory :: MyPresburgerFormula -> Maybe MyProp
checkMyPresburgerFormulaIsTheory = tryEvalFormula where
    tryEvalTerm :: PresburgerTerm -> Maybe MyNat
    tryEvalTerm (PresburgerTerm con coeffs) = if Map.null coeffs then pure con else Nothing
    tryEvalFormula :: MyPresburgerFormula -> Maybe MyProp
    tryEvalFormula (ValF b) = pure b
    tryEvalFormula (EqnF t1 t2) = pure (==) <*> tryEvalTerm t1 <*> tryEvalTerm t2
    tryEvalFormula (LtnF t1 t2) = pure (<) <*> tryEvalTerm t1 <*> tryEvalTerm t2
    tryEvalFormula (LeqF t1 t2) = pure (<=) <*> tryEvalTerm t1 <*> tryEvalTerm t2
    tryEvalFormula (GtnF t1 t2) = pure (>) <*> tryEvalTerm t1 <*> tryEvalTerm t2
    tryEvalFormula (ModF t1 r t2) = pure congruenceModulo <*> tryEvalTerm t1 <*> pure r <*> tryEvalTerm t2
    tryEvalFormula (NegF f1) = pure not <*> tryEvalFormula f1
    tryEvalFormula (DisF f1 f2) = pure (||) <*> tryEvalFormula f1 <*> tryEvalFormula f2
    tryEvalFormula (ConF f1 f2) = pure (&&) <*> tryEvalFormula f1 <*> tryEvalFormula f2
    tryEvalFormula (ImpF f1 f2) = pure (<=) <*> tryEvalFormula f1 <*> tryEvalFormula f2
    tryEvalFormula (IffF f1 f2) = pure (==) <*> tryEvalFormula f1 <*> tryEvalFormula f2
    tryEvalFormula (AllF y f1) = tryEvalFormula f1
    tryEvalFormula (ExsF y f1) = tryEvalFormula f1

insertFVsInPresburgerTermRep :: PresburgerTermRep -> Set.Set MyVar -> Set.Set MyVar
insertFVsInPresburgerTermRep = addFVs where
    addFVs :: PresburgerTermRep -> Set.Set MyVar -> Set.Set MyVar
    addFVs (IVar x) = Set.insert x
    addFVs (Zero) = id
    addFVs (Succ t1) = addFVs t1
    addFVs (Plus t1 t2) = addFVs t1 . addFVs t2

getFVsInMyPresburgerFormulaRep :: MyPresburgerFormulaRep -> Set.Set MyVar
getFVsInMyPresburgerFormulaRep = getFVs where
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

chi :: MyPresburgerFormulaRep -> MySubst -> MyVar
chi f sigma = succ (getMaxVarOf [ getMaxVarOf (insertFVsInPresburgerTermRep (applyMySubstToVar x sigma) Set.empty) | x <- Set.toAscList (getFVsInMyPresburgerFormulaRep f) ]) where
    getMaxVarOf :: Foldable container_of => container_of MyVar -> MyVar
    getMaxVarOf = foldr max 0

getFreshVar :: MyPresburgerFormulaRep -> MyVar
getFreshVar f = chi f nilMySubst

nilMySubst :: MySubst
nilMySubst z = IVar z

consMySubst :: (MyVar, PresburgerTermRep) -> MySubst -> MySubst
consMySubst (x, t) sigma z = if x == z then t else applyMySubstToVar z sigma

makeMySubst :: [(MyVar, PresburgerTermRep)] -> MySubst
makeMySubst = foldr consMySubst nilMySubst

applyMySubstToVar :: MyVar -> MySubst -> PresburgerTermRep
applyMySubstToVar x sigma = sigma x

runMySubst :: MySubst -> MyPresburgerFormulaRep -> MyPresburgerFormulaRep
runMySubst = flip applyMySubstToFormulaRep where
    applyMySubstToTermRep :: PresburgerTermRep -> MySubst -> PresburgerTermRep
    applyMySubstToTermRep (IVar x) = applyMySubstToVar x
    applyMySubstToTermRep (Zero) = pure Zero
    applyMySubstToTermRep (Succ t1) = pure Succ <*> applyMySubstToTermRep t1
    applyMySubstToTermRep (Plus t1 t2) = pure Plus <*> applyMySubstToTermRep t1 <*> applyMySubstToTermRep t2
    applyMySubstToFormulaRep :: MyPresburgerFormulaRep -> MySubst -> MyPresburgerFormulaRep
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
    applyMySubstToQuantifier :: MyPresburgerFormulaRep -> MySubst -> MyVar -> MyPresburgerFormulaRep
    applyMySubstToQuantifier (AllF y f1) sigma z = AllF z (applyMySubstToFormulaRep f1 (consMySubst (y, IVar z) sigma))
    applyMySubstToQuantifier (ExsF y f1) sigma z = ExsF z (applyMySubstToFormulaRep f1 (consMySubst (y, IVar z) sigma))

mapTermInPresburgerFormula :: (old_term -> term) -> PresburgerFormula old_term -> PresburgerFormula term
mapTermInPresburgerFormula = go where
    mkValF :: MyProp -> PresburgerFormula term
    mkValF b = ValF b
    mkEqnF :: term -> term -> PresburgerFormula term
    mkEqnF t1 t2 = t1 `seq` t2 `seq` EqnF t1 t2
    mkLtnF :: term -> term -> PresburgerFormula term
    mkLtnF t1 t2 = t1 `seq` t2 `seq` LtnF t1 t2
    mkLeqF :: term -> term -> PresburgerFormula term
    mkLeqF t1 t2 = t1 `seq` t2 `seq` LeqF t1 t2
    mkGtnF :: term -> term -> PresburgerFormula term
    mkGtnF t1 t2 = t1 `seq` t2 `seq` GtnF t1 t2
    mkModF :: term -> PositiveInteger -> term -> PresburgerFormula term
    mkModF t1 r t2 = t1 `seq` t2 `seq` ModF t1 r t2
    mkNegF :: PresburgerFormula term -> PresburgerFormula term
    mkNegF f1 = f1 `seq` NegF f1
    mkDisF :: PresburgerFormula term -> PresburgerFormula term -> PresburgerFormula term
    mkDisF f1 f2 = f1 `seq` f2 `seq` DisF f1 f2
    mkConF :: PresburgerFormula term -> PresburgerFormula term -> PresburgerFormula term
    mkConF f1 f2 = f1 `seq` f2 `seq` ConF f1 f2
    mkImpF :: PresburgerFormula term -> PresburgerFormula term -> PresburgerFormula term
    mkImpF f1 f2 = f1 `seq` f2 `seq` ImpF f1 f2
    mkIffF :: PresburgerFormula term -> PresburgerFormula term -> PresburgerFormula term
    mkIffF f1 f2 = f1 `seq` f2 `seq` IffF f1 f2
    mkAllF :: MyVar -> PresburgerFormula term -> PresburgerFormula term
    mkAllF y f1 = f1 `seq` AllF y f1
    mkExsF :: MyVar -> PresburgerFormula term -> PresburgerFormula term
    mkExsF y f1 = f1 `seq` ExsF y f1
    go :: (old_term -> term) -> PresburgerFormula old_term -> PresburgerFormula term
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
