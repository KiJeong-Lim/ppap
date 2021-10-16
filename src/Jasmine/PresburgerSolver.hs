module Jasmine.PresburgerSolver where

import qualified Data.List as List
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Y.Base
import Z.Algo.Function
import Z.Utils

type Var = MyNat

type Coefficient = Integer

data TermRep
    = IVar Var
    | Zero
    | Succ TermRep
    | Plus TermRep TermRep
    deriving (Eq)

data Term
    = Term 
        { getConstantTerm :: MyNat
        , getCoefficients :: Map.Map Var Coefficient
        }
    deriving (Eq)

data Formula term
    = ValF Bool
    | EqnF term term
    | LtnF term term
    | LeqF term term
    | GtnF term term
    | ModF term MyNat term
    | NegF (Formula term)
    | DisF (Formula term) (Formula term)
    | ConF (Formula term) (Formula term)
    | ImpF (Formula term) (Formula term)
    | IffF (Formula term) (Formula term)
    | AllF Var (Formula term)
    | ExsF Var (Formula term)
    deriving (Eq)

data Klass
    = KlassEqn !Coefficient !Term !Term
    | KlassLtn !Coefficient !Term !Term
    | KlassGtn !Coefficient !Term !Term
    | KlassMod !Coefficient !Term !MyNat !Term
    | KlassEtc !(Formula Term)
    deriving (Eq)

instance Show TermRep where
    showsPrec prec = dispatch where
        myPrecIs :: Precedence -> ShowS -> ShowS
        myPrecIs prec' ss = if prec > prec' then strstr "(" . ss . strstr ")" else ss
        dispatch :: TermRep -> ShowS
        dispatch (IVar x) = myPrecIs 11 $ showVar x
        dispatch (Zero) = myPrecIs 11 $ strstr "0"
        dispatch (Succ t1) = myPrecIs 11 $ strstr "S " . showsPrec 10 t1
        dispatch (Plus t1 t2) = myPrecIs 4 $ showsPrec 4 t1 . strstr " + " . showsPrec 5 t2

instance Show Term where
    showsPrec _ (Term con coeffs)
        | con == 0 = if Map.null coeffs then strstr "0" else ppunc " + " [ (if n > 1 then shows n . strstr " " else id) . showVar x | (x, n) <- Map.toAscList coeffs ]
        | otherwise = strcat [ (if n > 1 then shows n . strstr " " else id) . showVar x . strstr " + " | (x, n) <- Map.toAscList coeffs ] . shows con

instance Functor Formula where
    fmap f (ValF b) = ValF b
    fmap f (EqnF t1 t2) = EqnF (f t1) (f t2)
    fmap f (LtnF t1 t2) = LtnF (f t1) (f t2)
    fmap f (LeqF t1 t2) = LeqF (f t1) (f t2)
    fmap f (GtnF t1 t2) = GtnF (f t1) (f t2)
    fmap f (ModF t1 r t2) = ModF (f t1) r (f t2)
    fmap f (NegF f1) = NegF (fmap f f1)
    fmap f (DisF f1 f2) = DisF (fmap f f1) (fmap f f2)
    fmap f (ConF f1 f2) = ConF (fmap f f1) (fmap f f2)
    fmap f (ImpF f1 f2) = ImpF (fmap f f1) (fmap f f2)
    fmap f (IffF f1 f2) = IffF (fmap f f1) (fmap f f2)
    fmap f (AllF y f1) = AllF y (fmap f f1)
    fmap f (ExsF y f1) = ExsF y (fmap f f1)

instance Show term => Show (Formula term) where
    showsPrec prec = dispatch where
        myPrecIs :: Precedence -> ShowS -> ShowS
        myPrecIs prec' ss = if prec > prec' then strstr "(" . ss . strstr ")" else ss
        dispatch :: Show term => Formula term -> ShowS
        dispatch (ValF b1) = myPrecIs 11 $ strstr (if b1 then "~ _|_" else "_|_")
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
        dispatch (AllF y f1) = myPrecIs 8 $ strstr "forall " . showVar y . strstr ", " . showsPrec 8 f1
        dispatch (ExsF y f1) = myPrecIs 8 $ strstr "exists " . showVar y . strstr ", " . showsPrec 8 f1

showVar :: Var -> ShowS
showVar x = strstr "v" . shows x

runTermRep :: TermRep -> Term
runTermRep = go where
    mkTerm :: MyNat -> Map.Map Var Coefficient -> Term
    mkTerm con coeffs = con `seq` coeffs `seq` Term con coeffs
    go :: TermRep -> Term
    go (IVar x) = mkTerm 0 (Map.singleton x 1)
    go (Zero) = mkTerm 0 Map.empty
    go (Succ t1) = case go t1 of
        Term con1 coeffs1 -> mkTerm (succ con1) coeffs1
    go (Plus t1 t2) = case (go t1, go t2) of
        (Term con1 coeffs1, Term con2 coeffs2) -> mkTerm (con1 + con2) (foldr plusCoeff coeffs1 (Map.toAscList coeffs2))
    plusCoeff :: (Var, Coefficient) -> Map.Map Var Coefficient -> Map.Map Var Coefficient
    plusCoeff (x, n) = Map.alter (maybe (callWithStrictArg Just n) (\n' -> callWithStrictArg Just (n + n'))) x

eliminateQuantifier :: Formula Term -> Formula Term
eliminateQuantifier = eliminateOneByOne where
    mkTerm :: MyNat -> Map.Map Var Coefficient -> Term
    mkTerm con coeffs = con `seq` coeffs `seq` Term con coeffs
    multiplyTerm :: MyNat -> Term -> Term
    multiplyTerm k t
        | k < 0 = error "multiplyTerm: negative input"
        | k == 0 = mkZero
        | k == 1 = t
        | otherwise = mkTerm (getConstantTerm t * k) (Map.map (\n -> n * k) (getCoefficients t))
    orcat :: [Formula Term] -> Formula Term
    orcat [] = mkBotF
    orcat (f : fs) = List.foldl' mkDisF f fs
    andcat :: [Formula Term] -> Formula Term
    andcat = foldr mkConF mkTopF
    getLCM :: MyNat -> MyNat -> MyNat
    getLCM x y = (x * y) `div` (getGCD x y)
    unNum :: Term -> Maybe MyNat
    unNum t = if Map.null (getCoefficients t) then Nothing else return (getConstantTerm t)
    mkNum :: MyNat -> Term
    mkNum n = mkTerm n Map.empty
    mkValF :: Bool -> Formula Term
    mkValF b1 = b1 `seq` ValF b1
    mkIVar :: Var -> Term
    mkIVar x = mkTerm 0 (Map.singleton x 1)
    mkZero :: Term
    mkZero = mkNum 0
    mkSucc :: Term -> Term
    mkSucc (Term con coeffs) = mkTerm (succ con) coeffs
    mkPlus :: Term -> Term -> Term
    mkPlus (Term con1 coeffs1) (Term con2 coeffs2) = mkTerm (con1 + con2) (foldr go coeffs1 (Map.toAscList coeffs2)) where
        go :: (Var, Coefficient) -> Map.Map Var Coefficient -> Map.Map Var Coefficient
        go (x, n) = Map.alter (maybe (callWithStrictArg Just n) (\n' -> callWithStrictArg Just (n + n'))) x
    mkEqnF :: Term -> Term -> Formula Term
    mkEqnF t1 t2 = if t1 == t2 then mkTopF else t1 `seq` t2 `seq` EqnF t1 t2
    mkLtnF :: Term -> Term -> Formula Term
    mkLtnF t1 t2
        | getCoefficients t1 == getCoefficients t2 = mkValF (getConstantTerm t1 < getConstantTerm t2)
        | otherwise = t1 `seq` t2 `seq` LtnF t1 t2
    mkModF :: Term -> MyNat -> Term -> Formula Term
    mkModF t1 r t2
        | r <= 0 = error "mkModF: r must be positive!"
        | r == 1 = mkTopF
        | Map.null (getCoefficients t1) && Map.null (getCoefficients t2) = mkValF ((getConstantTerm t1 `mod` r) == (getConstantTerm t2 `mod` r))
        | otherwise = t1 `seq` t2 `seq` ModF t1 r t2
    mkLeqF :: Term -> Term -> Formula Term
    mkLeqF t1 t2 = mkDisF (mkEqnF t1 t2) (mkLtnF t1 t2)
    mkGtnF :: Term -> Term -> Formula Term
    mkGtnF t1 t2 = mkLtnF t2 t1
    mkTopF :: Formula Term
    mkTopF = mkValF True
    mkBotF :: Formula Term
    mkBotF = mkValF False
    mkNegF :: Formula Term -> Formula Term
    mkNegF (ValF b1) = mkValF (not b1)
    mkNegF (NegF f1) = f1
    mkNegF f1 = NegF f1
    mkDisF :: Formula Term -> Formula Term -> Formula Term
    mkDisF (ValF b1) f2 = if b1 then mkTopF else f2
    mkDisF f1 (ValF b2) = if b2 then mkTopF else f1
    mkDisF f1 f2 = DisF f1 f2
    mkConF :: Formula Term -> Formula Term -> Formula Term
    mkConF (ValF b1) f2 = if b1 then f2 else mkBotF
    mkConF f1 (ValF b2) = if b2 then f1 else mkBotF
    mkConF f1 f2 = ConF f1 f2
    mkImpF :: Formula Term -> Formula Term -> Formula Term
    mkImpF f1 f2 = mkDisF (mkNegF f1) f2
    mkIffF :: Formula Term -> Formula Term -> Formula Term
    mkIffF f1 f2 = mkConF (mkImpF f1 f2) (mkImpF f2 f1)
    mkAllF :: Var -> Formula Term -> Formula Term
    mkAllF y f1 = mkNegF (mkExsF y (mkNegF f1))
    mkExsF :: Var -> Formula Term -> Formula Term
    mkExsF y f1 = f1 `seq` ExsF y f1
    eliminateOneByOne :: Formula Term -> Formula Term
    eliminateOneByOne = asterify . simplify where
        simplify :: Formula Term -> Formula Term
        simplify (ValF b1) = mkValF b1
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
        asterify :: Formula Term -> Formula Term
        asterify (NegF f1) = mkNegF (asterify f1)
        asterify (ConF f1 f2) = mkConF (asterify f1) (asterify f2)
        asterify (DisF f1 f2) = mkDisF (asterify f1) (asterify f2)
        asterify (ExsF y f1) = eliminateExsF y (asterify f1)
        asterify atom_f = atom_f
    eliminateExsF :: Var -> Formula Term -> Formula Term
    eliminateExsF = curry step1 where
        step1 :: (Var, Formula Term) -> Formula Term
        step1 = myMain where
            runNeg :: Formula Term -> Formula Term
            runNeg (ValF b1) = mkValF (not b1)
            runNeg (EqnF t1 t2) = mkDisF (mkLtnF t1 t2) (mkGtnF t1 t2)
            runNeg (LtnF t1 t2) = mkDisF (mkEqnF t1 t2) (mkGtnF t1 t2)
            runNeg (ModF t1 r t2) = orcat [ mkModF t1 r (mkPlus t2 (mkNum i)) | i <- [1 .. r - 1] ]
            runNeg (NegF f1) = f1
            runNeg (DisF f1 f2) = mkConF (runNeg f1) (runNeg f2)
            runNeg (ConF f1 f2) = mkDisF (runNeg f1) (runNeg f2)
            removeNegation :: Formula Term -> Formula Term
            removeNegation = go where
                go :: Formula Term -> Formula Term
                go (NegF f1) = runNeg (go f1)
                go (DisF f1 f2) = mkDisF (go f1) (go f2)
                go (ConF f1 f2) = mkConF (go f1) (go f2)
                go atom_f = atom_f
            makeDNFfromNoNeg :: Formula Term -> [[Formula Term]]
            makeDNFfromNoNeg (DisF f1 f2) = makeDNFfromNoNeg f1 ++ makeDNFfromNoNeg f2
            makeDNFfromNoNeg (ConF f1 f2) = [ fs1 ++ fs2 | fs1 <- makeDNFfromNoNeg f1, fs2 <- makeDNFfromNoNeg f2 ]
            makeDNFfromNoNeg atom_f = [one atom_f]
            myMain :: (Var, Formula Term) -> Formula Term
            myMain (x, psi) = orcat [ step2 x conjs | conjs <- makeDNFfromNoNeg (removeNegation psi) ]
        step2 :: Var -> [Formula Term] -> Formula Term
        step2 x = myMain where
            mkKlasses :: [Formula Term] -> [Klass]
            mkKlasses = map mkKlass where
                extractCoefficient :: Term -> (MyNat, Term)
                extractCoefficient t = case Map.lookup x (getCoefficients t) of
                    Nothing -> (0, t)
                    Just n -> (n, mkTerm (getConstantTerm t) (Map.delete x (getCoefficients t)))
                mkKlass :: Formula Term -> Klass
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
            standardizeCoefficient :: [Klass] -> Either [Klass] (MyNat, [Klass])
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
                theStandardizedKlasses :: MyNat -> [Klass]
                theStandardizedKlasses theLCM = map myLoop your_klasses where
                    myLoop :: Klass -> Klass
                    myLoop (KlassEqn m t1 t2) = KlassEqn theLCM (multiplyTerm (theLCM `div` m) t1) (multiplyTerm (theLCM `div` m) t2)
                    myLoop (KlassLtn m t1 t2) = KlassLtn theLCM (multiplyTerm (theLCM `div` m) t1) (multiplyTerm (theLCM `div` m) t2)
                    myLoop (KlassGtn m t1 t2) = KlassGtn theLCM (multiplyTerm (theLCM `div` m) t1) (multiplyTerm (theLCM `div` m) t2)
                    myLoop (KlassMod m t1 r t2) = KlassMod theLCM (multiplyTerm (theLCM `div` m) t1) (r * (theLCM `div` m)) (multiplyTerm (theLCM `div` m) t2)
                    myLoop (KlassEtc f) = KlassEtc f
            myMain :: [Formula Term] -> Formula Term
            myMain conjs = case standardizeCoefficient (mkKlasses conjs) of
                Left my_klasses -> andcat [ f | KlassEtc f <- my_klasses ]
                Right (m, my_klasses) -> mkConF (andcat [ f | KlassEtc f <- my_klasses ]) (step3 [ (t1, t2) | KlassEqn _ t1 t2 <- my_klasses ] [ (t1, t2) | KlassLtn _ t1 t2 <- my_klasses ] ((mkNum 1, mkNum 0) : [ (t1, t2) | KlassGtn _ t1 t2 <- my_klasses ]) ((m, (mkNum 0, mkNum 0)) : [ (r, (t1, t2)) | KlassMod _ t1 r t2 <- my_klasses ]))
        step3 :: [(Term, Term)] -> [(Term, Term)] -> [(Term, Term)] -> [(MyNat, (Term, Term))] -> Formula Term
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

destiny :: Formula Term -> Maybe Bool
destiny = tryEvalFormula where
    tryEvalTerm :: Term -> Maybe MyNat
    tryEvalTerm (Term con coeffs) = if Map.null coeffs then pure con else Nothing
    myEqn :: MyNat -> MyNat -> Bool
    myEqn n1 n2 = n1 == n2
    myLtn :: MyNat -> MyNat -> Bool
    myLtn n1 n2 = n1 < n2
    myLeq :: MyNat -> MyNat -> Bool
    myLeq n1 n2 = n1 <= n2
    myGtn :: MyNat -> MyNat -> Bool
    myGtn n1 n2 = n1 > n2
    myMod :: MyNat -> MyNat -> MyNat -> Bool
    myMod n1 r n2 = n1 `mod` r == n2 `mod` r
    myNeg :: Bool -> Bool
    myNeg b1 = not b1
    myDis :: Bool -> Bool -> Bool
    myDis b1 b2 = b1 || b2
    myCon :: Bool -> Bool -> Bool
    myCon b1 b2 = b1 && b2
    myImp :: Bool -> Bool -> Bool
    myImp b1 b2 = b1 <= b2
    myIff :: Bool -> Bool -> Bool
    myIff b1 b2 = b1 == b2
    tryEvalFormula :: Formula Term -> Maybe Bool
    tryEvalFormula (ValF b1) = pure b1
    tryEvalFormula (EqnF t1 t2) = pure myEqn <*> tryEvalTerm t1 <*> tryEvalTerm t2
    tryEvalFormula (LtnF t1 t2) = pure myLtn <*> tryEvalTerm t1 <*> tryEvalTerm t2
    tryEvalFormula (LeqF t1 t2) = pure myLeq <*> tryEvalTerm t1 <*> tryEvalTerm t2
    tryEvalFormula (GtnF t1 t2) = pure myGtn <*> tryEvalTerm t1 <*> tryEvalTerm t2
    tryEvalFormula (ModF t1 r t2) = pure myMod <*> tryEvalTerm t1 <*> pure r <*> tryEvalTerm t2
    tryEvalFormula (NegF f1) = pure myNeg <*> tryEvalFormula f1
    tryEvalFormula (DisF f1 f2) = pure myDis <*> tryEvalFormula f1 <*> tryEvalFormula f2
    tryEvalFormula (ConF f1 f2) = pure myCon <*> tryEvalFormula f1 <*> tryEvalFormula f2
    tryEvalFormula (ImpF f1 f2) = pure myImp <*> tryEvalFormula f1 <*> tryEvalFormula f2
    tryEvalFormula _ = Nothing
