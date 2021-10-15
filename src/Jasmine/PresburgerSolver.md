# PresburgerSolver

## The 1st version

```hs
module Jasmine.PresburgerSolver where

import qualified Data.List as List
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Y.Base
import Z.Algo.Function
import Z.Utils

type Var = MyNat

type Coefficient = Integer

data Term
    = Term 
        { getConstantTerm :: MyNat
        , getCoefficients :: Map.Map Var Coefficient
        }
    deriving (Eq)

data Formula
    = ValF Bool
    | EqnF Term Term
    | LtnF Term Term
    | ModF Term MyNat Term
    | NegF Formula
    | DisF Formula Formula
    | ConF Formula Formula
    | ImpF Formula Formula
    | AllF Var Formula
    | ExsF Var Formula
    deriving (Eq)

data Klass
    = KlassEqn !Coefficient !Term !Term
    | KlassLtn !Coefficient !Term !Term
    | KlassGtn !Coefficient !Term !Term
    | KlassMod !Coefficient !Term !MyNat !Term
    | KlassEtc !Formula
    deriving (Eq)

instance Show Term where
    showsPrec _ (Term con coeffs)
        | con == 0 = ppunc " + " [ shows n . strstr " " . showVar x | (x, n) <- Map.toAscList coeffs ]
        | otherwise = strcat [ shows n . strstr " " . showVar x . strstr " + " | (x, n) <- Map.toAscList coeffs ] . shows con

instance Show Formula where
    showsPrec prec = dispatch where
        myPrecIs :: Precedence -> ShowS -> ShowS
        myPrecIs prec' ss = if prec > prec' then strstr "(" . ss . strstr ")" else ss
        dispatch :: Formula -> ShowS
        dispatch (ValF b1) = myPrecIs 11 $ strstr (if b1 then "~ _|_" else "_|_")
        dispatch (EqnF t1 t2) = myPrecIs 9 $ shows t1 . strstr " = " . shows t2
        dispatch (LtnF t1 t2) = myPrecIs 9 $ shows t1 . strstr " < " . shows t2
        dispatch (ModF t1 r t2) = myPrecIs 9 $ shows t1 . strstr " ==_{" . shows r . strstr "} " . shows t2
        dispatch (NegF f1) = myPrecIs 8 $ strstr "~ " . showsPrec 9 f1
        dispatch (DisF f1 f2) = myPrecIs 6 $ showsPrec 6 f1 . strstr " \\/ " . showsPrec 7 f2
        dispatch (ConF f1 f2) = myPrecIs 7 $ showsPrec 7 f1 . strstr " /\\ " . showsPrec 8 f2
        dispatch (ImpF f1 f2) = myPrecIs 0 $ showsPrec 1 f1 . strstr " -> " . showsPrec 0 f2
        dispatch (AllF y f1) = myPrecIs 8 $ strstr "forall " . showVar y . strstr ", " . showsPrec 8 f1
        dispatch (ExsF y f1) = myPrecIs 8 $ strstr "exists " . showVar y . strstr ", " . showsPrec 8 f1

eliminateQuantifier :: Formula -> Formula
eliminateQuantifier = eliminateOneByOne where
    eliminateOneByOne :: Formula -> Formula
    eliminateOneByOne = asterify . simplify where
        simplify :: Formula -> Formula
        simplify (NegF f1) = mkNegF (simplify f1)
        simplify (DisF f1 f2) = mkDisF (simplify f1) (simplify f2)
        simplify (ConF f1 f2) = mkConF (simplify f1) (simplify f1)
        simplify (ImpF f1 f2) = mkDisF (mkNegF (simplify f1)) (simplify f2) 
        simplify (AllF y f1) = mkNegF (mkExsF y (mkNegF (simplify f1)))
        simplify (ExsF y f1) = mkExsF y (simplify f1)
        simplify atom_f = atom_f
        asterify :: Formula -> Formula
        asterify (NegF f1) = mkNegF (asterify f1)
        asterify (ConF f1 f2) = mkConF (asterify f1) (asterify f2)
        asterify (DisF f1 f2) = mkDisF (asterify f1) (asterify f2)
        asterify (ExsF y f1) = eliminateExsF y (asterify f1)
        asterify atom_f = atom_f
    eliminateExsF :: Var -> Formula -> Formula
    eliminateExsF = curry step1 where
        runNeg :: Formula -> Formula
        runNeg (ValF b1) = mkValF (not b1)
        runNeg (EqnF t1 t2) = mkDisF (mkLtnF t1 t2) (mkGtnF t1 t2)
        runNeg (LtnF t1 t2) = mkDisF (mkEqnF t1 t2) (mkGtnF t1 t2)
        runNeg (ModF t1 r t2) = orcat [ mkModF t1 r (mkPlus t2 (mkNum i)) | i <- [1 .. r - 1] ]
        runNeg (NegF f1) = f1
        runNeg (DisF f1 f2) = mkConF (runNeg f1) (runNeg f2)
        runNeg (ConF f1 f2) = mkDisF (runNeg f1) (runNeg f2)
        step1 :: (Var, Formula) -> Formula
        step1 = myMain where
            removeNegation :: Formula -> Formula
            removeNegation = go where
                go :: Formula -> Formula
                go (NegF f1) = runNeg (go f1)
                go (DisF f1 f2) = mkDisF (go f1) (go f2)
                go (ConF f1 f2) = mkConF (go f1) (go f2)
                go atom_f = atom_f
            makeDNFfromNoNeg :: Formula -> [[Formula]]
            makeDNFfromNoNeg (DisF f1 f2) = makeDNFfromNoNeg f1 ++ makeDNFfromNoNeg f2
            makeDNFfromNoNeg (ConF f1 f2) = [ fs1 ++ fs2 | fs1 <- makeDNFfromNoNeg f1, fs2 <- makeDNFfromNoNeg f2 ]
            makeDNFfromNoNeg atom_f = [one atom_f]
            myMain :: (Var, Formula) -> Formula
            myMain (x, psi) = orcat [ step2 x conjs | conjs <- makeDNFfromNoNeg (removeNegation psi) ]
        step2 :: Var -> [Formula] -> Formula
        step2 x = myMain where
            mkKlasses :: [Formula] -> [Klass]
            mkKlasses = map mkKlass where
                extractCoefficient :: Term -> (MyNat, Term)
                extractCoefficient t = case Map.lookup x (getCoefficients t) of
                    Nothing -> (0, t)
                    Just n -> (n, mkTerm (getConstantTerm t) (Map.delete x (getCoefficients t)))
                mkKlass :: Formula -> Klass
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
            myMain :: [Formula] -> Formula
            myMain conjs = case standardizeCoefficient (mkKlasses conjs) of
                Left my_klasses -> andcat [ f | KlassEtc f <- my_klasses ]
                Right (m, my_klasses) -> mkConF (andcat [ f | KlassEtc f <- my_klasses ]) (step3 [ (t1, t2) | KlassEqn _ t1 t2 <- my_klasses ] [ (t1, t2) | KlassLtn _ t1 t2 <- my_klasses ] ((mkNum 1, mkNum 0) : [ (t1, t2) | KlassGtn _ t1 t2 <- my_klasses ]) ((m, (mkNum 0, mkNum 0)) : [ (r, (t1, t2)) | KlassMod _ t1 r t2 <- my_klasses ]))
        step3 :: [(Term, Term)] -> [(Term, Term)] -> [(Term, Term)] -> [(MyNat, (Term, Term))] -> Formula
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

showVar :: Var -> ShowS
showVar x = strstr "v" . shows x

mkTerm :: MyNat -> Map.Map Var Coefficient -> Term
mkTerm con coeffs = con `seq` coeffs `seq` Term con coeffs

multiplyTerm :: MyNat -> Term -> Term
multiplyTerm k t
    | k < 0 = error "multiplyTerm: negative input"
    | k == 0 = mkZero
    | k == 1 = t
    | otherwise = mkTerm (getConstantTerm t * k) (Map.map (\n -> n * k) (getCoefficients t))

orcat :: [Formula] -> Formula
orcat [] = mkBotF
orcat (f : fs) = List.foldl' mkDisF f fs

andcat :: [Formula] -> Formula
andcat = foldr mkConF mkTopF

getLCM :: MyNat -> MyNat -> MyNat
getLCM x y = (x * y) `div` (getGCD x y)

unNum :: Term -> Maybe MyNat
unNum t = if Map.null (getCoefficients t) then Nothing else return (getConstantTerm t)

mkNum :: MyNat -> Term
mkNum n = mkTerm n Map.empty

mkLeqF :: Term -> Term -> Formula
mkLeqF t1 t2 = mkDisF (mkEqnF t1 t2) (mkLtnF t1 t2)

mkGtnF :: Term -> Term -> Formula
mkGtnF t1 t2 = mkLtnF t2 t1

mkValF :: Bool -> Formula
mkValF b1 = b1 `seq` ValF b1

mkTopF :: Formula
mkTopF = mkValF True

mkBotF :: Formula
mkBotF = mkValF False

mkIffF :: Formula -> Formula -> Formula
mkIffF f1 f2 = mkConF (mkImpF f1 f2) (mkImpF f2 f1)

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

mkEqnF :: Term -> Term -> Formula
mkEqnF t1 t2 = if t1 == t2 then mkTopF else t1 `seq` t2 `seq` EqnF t1 t2

mkLtnF :: Term -> Term -> Formula
mkLtnF t1 t2
    | getCoefficients t1 == getCoefficients t2 = mkValF (getConstantTerm t1 < getConstantTerm t2)
    | otherwise = t1 `seq` t2 `seq` LtnF t1 t2

mkModF :: Term -> MyNat -> Term -> Formula
mkModF t1 r t2
    | r <= 0 = error "mkModF: r must be positive!"
    | r == 1 = mkTopF
    | Map.null (getCoefficients t1) && Map.null (getCoefficients t2) = mkValF ((getConstantTerm t1 `mod` r) == (getConstantTerm t2 `mod` r))
    | otherwise = t1 `seq` t2 `seq` ModF t1 r t2

mkNegF :: Formula -> Formula
mkNegF (ValF b1) = mkValF (not b1)
mkNegF (NegF f1) = f1
mkNegF f1 = NegF f1

mkDisF :: Formula -> Formula -> Formula
mkDisF (ValF b1) f2 = if b1 then mkTopF else f2
mkDisF f1 (ValF b2) = if b2 then mkTopF else f1
mkDisF f1 f2 = DisF f1 f2

mkConF :: Formula -> Formula -> Formula
mkConF (ValF b1) f2 = if b1 then f2 else mkBotF
mkConF f1 (ValF b2) = if b2 then f1 else mkBotF
mkConF f1 f2 = ConF f1 f2

mkImpF :: Formula -> Formula -> Formula
mkImpF f1 f2 = f1 `seq` f2 `seq` ImpF f1 f2

mkAllF :: Var -> Formula -> Formula
mkAllF y f1 = f1 `seq` AllF y f1

mkExsF :: Var -> Formula -> Formula
mkExsF y f1 = f1 `seq` ExsF y f1

destiny :: Formula -> Bool
destiny = maybe False id . tryEvalFormula where
    tryEvalTerm :: Term -> Maybe MyNat
    tryEvalTerm (Term con coeffs) = if Map.null coeffs then return con else Nothing
    myEqn :: MyNat -> MyNat -> Bool
    myEqn n1 n2 = n1 == n2
    myLtn :: MyNat -> MyNat -> Bool
    myLtn n1 n2 = n1 < n2
    myMod :: MyNat -> MyNat -> MyNat -> Bool
    myMod n1 r n2 = (n1 `mod` r) == (n2 `mod` r)
    myNeg :: Bool -> Bool
    myNeg b1 = not b1
    myDis :: Bool -> Bool -> Bool
    myDis b1 b2 = b1 || b2
    myCon :: Bool -> Bool -> Bool
    myCon b1 b2 = b1 && b2
    myImp :: Bool -> Bool -> Bool
    myImp b1 b2 = (not b1) || b2
    tryEvalFormula :: Formula -> Maybe Bool
    tryEvalFormula (ValF b1) = pure b1 
    tryEvalFormula (EqnF t1 t2) = pure myEqn <*> tryEvalTerm t1 <*> tryEvalTerm t2
    tryEvalFormula (LtnF t1 t2) = pure myLtn <*> tryEvalTerm t1 <*> tryEvalTerm t2
    tryEvalFormula (ModF t1 r t2) = pure myMod <*> tryEvalTerm t1 <*> pure r <*> tryEvalTerm t2
    tryEvalFormula (NegF f1) = pure myNeg <*> tryEvalFormula f1
    tryEvalFormula (DisF f1 f2) = pure myDis <*> tryEvalFormula f1 <*> tryEvalFormula f2
    tryEvalFormula (ConF f1 f2) = pure myCon <*> tryEvalFormula f1 <*> tryEvalFormula f2
    tryEvalFormula (ImpF f1 f2) = pure myImp <*> tryEvalFormula f1 <*> tryEvalFormula f2
    tryEvalFormula _ = Nothing

```

- References:

1. `Fundamentals of Mathematical Logic` by `Peter G. Hinman`
