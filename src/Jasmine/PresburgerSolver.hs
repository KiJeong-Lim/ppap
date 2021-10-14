module Jasmine.PresburgerSolver where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Z.Algo.Function
import Z.Utils

type Var = MyNat

type Subst = Var -> Term

data Term
    = IVar Var
    | Zero
    | Succ Term
    | Plus Term Term
    deriving (Eq)

data Formula
    = EqnF Term Term
    | LtnF Term Term
    | ModF Term MyNat Term
    | NegF Formula
    | DisF Formula Formula
    | ConF Formula Formula
    | ImpF Formula Formula
    | AllF Var Formula
    | ExsF Var Formula
    deriving (Eq)

instance Show Term where
    showsPrec prec = dispatch where
        myPrecIs :: Precedence -> ShowS -> ShowS
        myPrecIs prec' ss = if prec > prec' then showChar '(' . ss . showChar ')' else ss
        dispatch :: Term -> ShowS
        dispatch (IVar x) = myPrecIs 11 $ showVar x
        dispatch (Zero) = myPrecIs 11 $ showString "0"
        dispatch (Succ t1) = myPrecIs 10 $ showString "S " . showsPrec 11 t1
        dispatch (Plus t1 t2) = myPrecIs 4 $ showsPrec 4 t1 . showString " + " . showsPrec 5 t2

instance Show Formula where
    showsPrec prec = dispatch where
        myPrecIs :: Precedence -> ShowS -> ShowS
        myPrecIs prec' ss = if prec > prec' then showChar '(' . ss . showChar ')' else ss
        dispatch :: Formula -> ShowS
        dispatch (EqnF t1 t2) = myPrecIs 3 $ showsPrec 4 t1 . showString " = " . showsPrec 4 t2
        dispatch (LtnF t1 t2) = myPrecIs 3 $ showsPrec 4 t1 . showString " < " . showsPrec 4 t2
        dispatch (ModF t1 r t2) = myPrecIs 3 $ showsPrec 4 t1 . showString " ==_{" . showsPrec 0 r . showString "} " . showsPrec 4 t2
        dispatch (NegF f1) = myPrecIs 3 $ showString "~ " . showsPrec 3 f1
        dispatch (DisF f1 f2) = myPrecIs 1 $ showsPrec 1 f1 . showString " \\/ " . showsPrec 2 f2
        dispatch (ConF f1 f2) = myPrecIs 2 $ showsPrec 2 f1 . showString " /\\ " . showsPrec 3 f2
        dispatch (ImpF f1 f2) = myPrecIs 0 $ showsPrec 1 f1 . showString " -> " . showsPrec 0 f2
        dispatch (AllF y f1) = myPrecIs 0 $ showString "forall " . showVar y . showString ", " . showsPrec 0 f1
        dispatch (ExsF y f1) = myPrecIs 0 $ showString "exists " . showVar y . showString ", " . showsPrec 0 f1

eliminateQuantifier :: Formula -> Formula
eliminateQuantifier = asterify . simplify where
    simplify :: Formula -> Formula
    simplify (NegF f1) = mkNegF (simplify f1)
    simplify (DisF f1 f2) = mkDisF (simplify f1) (simplify f2)
    simplify (ConF f1 f2) = mkNegF (mkDisF (mkNegF (simplify f1)) (mkNegF (simplify f2)))
    simplify (ImpF f1 f2) = mkDisF (mkNegF (simplify f1)) (simplify f2) 
    simplify (AllF y f1) = mkNegF (mkExsF y (mkNegF (simplify f1)))
    simplify (ExsF y f1) = mkExsF y (simplify f1)
    simplify atom_f1 = atom_f1
    asterify :: Formula -> Formula
    asterify (NegF f1) = mkNegF (asterify f1)
    asterify (DisF f1 f2) = mkDisF (asterify f1) (asterify f2)
    asterify (ExsF y f1) = eliminateQuantifierExsF y (asterify f1)
    asterify atom_f1 = atom_f1

eliminateQuantifierExsF :: Var -> Formula -> Formula
eliminateQuantifierExsF = curry go where
    go :: (Var, Formula) -> Formula
    go = undefined

showVar :: Var -> ShowS
showVar x = showString "v" . showsPrec 0 x

mkSubst :: [(Var, Term)] -> Subst
mkSubst = foldr consSubst nilSubst

mkNum :: Int -> Term
mkNum n = if n < 0 then error "mkNum: negative input" else iterate mkSucc mkZero !! n

mkBotF :: Formula
mkBotF = mkEqnF (mkNum 0) (mkNum 1)

mkIffF :: Formula -> Formula -> Formula
mkIffF f1 f2 = mkConF (mkImpF f1 f2) (mkImpF f2 f1)

mkIVar :: Var -> Term
mkIVar x = if x < 0 then error "mkIVar: negative input" else IVar x

mkZero :: Term
mkZero = Zero

mkSucc :: Term -> Term
mkSucc t1 = t1 `seq` Succ t1

mkPlus :: Term -> Term -> Term
mkPlus t1 t2 = t1 `seq` t2 `seq` Plus t1 t2

mkEqnF :: Term -> Term -> Formula
mkEqnF t1 t2 = t1 `seq` t2 `seq` EqnF t1 t2

mkLtnF :: Term -> Term -> Formula
mkLtnF t1 t2 = t1 `seq` t2 `seq` LtnF t1 t2

mkModF :: Term -> MyNat -> Term -> Formula
mkModF t1 r t2 = if r > 0 then t1 `seq` t2 `seq` ModF t1 r t2 else error "mkModF: r must be positive!"

mkNegF :: Formula -> Formula
mkNegF f1 = f1 `seq` NegF f1

mkDisF :: Formula -> Formula -> Formula
mkDisF f1 f2 = f1 `seq` f2 `seq` DisF f1 f2

mkConF :: Formula -> Formula -> Formula
mkConF f1 f2 = f1 `seq` f2 `seq` ConF f1 f2

mkImpF :: Formula -> Formula -> Formula
mkImpF f1 f2 = f1 `seq` f2 `seq` ImpF f1 f2

mkAllF :: Var -> Formula -> Formula
mkAllF y f1 = f1 `seq` AllF y f1

mkExsF :: Var -> Formula -> Formula
mkExsF y f1 = f1 `seq` ExsF y f1

nilSubst :: Subst
nilSubst x = mkIVar x

consSubst :: (Var, Term) -> Subst -> Subst
consSubst (z, t) sigma x = if z == x then t else applySubstOnVar x sigma

substitute :: (Var, Term) -> Formula -> Formula
substitute = runSubst . mkSubst . one

runSubst :: Subst -> Formula -> Formula
runSubst = flip applySubstOnFormula where
    applySubstOnTerm :: Term -> Subst -> Term
    applySubstOnTerm (IVar x) = applySubstOnVar x
    applySubstOnTerm (Zero) = pure mkZero
    applySubstOnTerm (Succ t1) = pure mkSucc <*> applySubstOnTerm t1
    applySubstOnTerm (Plus t1 t2) = pure mkPlus <*> applySubstOnTerm t1 <*> applySubstOnTerm t2
    applySubstOnFormula :: Formula -> Subst -> Formula
    applySubstOnFormula (EqnF t1 t2) = pure mkEqnF <*> applySubstOnTerm t1 <*> applySubstOnTerm t2
    applySubstOnFormula (LtnF t1 t2) = pure mkLtnF <*> applySubstOnTerm t1 <*> applySubstOnTerm t2
    applySubstOnFormula (ModF t1 r t2) = pure mkModF <*> applySubstOnTerm t1 <*> pure r <*> applySubstOnTerm t2
    applySubstOnFormula (NegF f1) = pure mkNegF <*> applySubstOnFormula f1
    applySubstOnFormula (DisF f1 f2) = pure mkDisF <*> applySubstOnFormula f1 <*> applySubstOnFormula f2
    applySubstOnFormula (ConF f1 f2) = pure mkConF <*> applySubstOnFormula f1 <*> applySubstOnFormula f2
    applySubstOnFormula (ImpF f1 f2) = pure mkImpF <*> applySubstOnFormula f1 <*> applySubstOnFormula f2
    applySubstOnFormula f = applySubstOnBinder f <*> chi f
    applySubstOnBinder :: Formula -> Subst -> Var -> Formula
    applySubstOnBinder (AllF y f1) sigma z = mkAllF z (applySubstOnFormula f1 (consSubst (y, mkIVar z) sigma))
    applySubstOnBinder (ExsF y f1) sigma z = mkExsF z (applySubstOnFormula f1 (consSubst (y, mkIVar z) sigma))

chi :: Formula -> Subst -> Var
chi f sigma = succ (maxOf [ maxOf (addFVsOfTerm (applySubstOnVar x sigma) Set.empty) | x <- Set.toAscList (getFVs f) ]) where
    maxOf :: Foldable f => f Var -> Var
    maxOf = foldr max 0

chi0 :: Formula -> Var
chi0 f = chi f nilSubst

getFVs :: Formula -> Set.Set Var
getFVs (EqnF t1 t2) = addFVsOfTerm t1 (addFVsOfTerm t2 Set.empty)
getFVs (LtnF t1 t2) = addFVsOfTerm t1 (addFVsOfTerm t2 Set.empty)
getFVs (ModF t1 r t2) = addFVsOfTerm t1 (addFVsOfTerm t2 Set.empty)
getFVs (NegF f1) = getFVs f1
getFVs (DisF f1 f2) = getFVs f1 `Set.union` getFVs f2
getFVs (ConF f1 f2) = getFVs f1 `Set.union` getFVs f2
getFVs (ImpF f1 f2) = getFVs f1 `Set.union` getFVs f2
getFVs (AllF y f1) = Set.delete y (getFVs f1)
getFVs (ExsF y f1) = Set.delete y (getFVs f1)

addFVsOfTerm :: Term -> Set.Set Var -> Set.Set Var
addFVsOfTerm (IVar x) = Set.insert x
addFVsOfTerm (Zero) = id
addFVsOfTerm (Succ t1) = addFVsOfTerm t1
addFVsOfTerm (Plus t1 t2) = addFVsOfTerm t1 . addFVsOfTerm t2

destiny :: Formula -> Bool
destiny = fromJust . tryEvalFormula where
    myZero :: MyNat
    myZero = 0
    mySucc :: MyNat -> MyNat
    mySucc n1 = succ n1
    myPlus :: MyNat -> MyNat -> MyNat
    myPlus n1 n2 = n1 + n2
    tryEvalTerm :: Term -> Maybe MyNat
    tryEvalTerm (Zero) = pure myZero
    tryEvalTerm (Succ t1) = pure mySucc <*> tryEvalTerm t1
    tryEvalTerm (Plus t1 t2) = pure myPlus <*> tryEvalTerm t1 <*> tryEvalTerm t2
    tryEvalTerm _ = Nothing
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
    tryEvalFormula (EqnF t1 t2) = pure myEqn <*> tryEvalTerm t1 <*> tryEvalTerm t2
    tryEvalFormula (LtnF t1 t2) = pure myLtn <*> tryEvalTerm t1 <*> tryEvalTerm t2
    tryEvalFormula (ModF t1 r t2) = pure myMod <*> tryEvalTerm t1 <*> pure r <*> tryEvalTerm t2
    tryEvalFormula (NegF f1) = pure myNeg <*> tryEvalFormula f1
    tryEvalFormula (DisF f1 f2) = pure myDis <*> tryEvalFormula f1 <*> tryEvalFormula f2
    tryEvalFormula (ConF f1 f2) = pure myCon <*> tryEvalFormula f1 <*> tryEvalFormula f2
    tryEvalFormula (ImpF f1 f2) = pure myImp <*> tryEvalFormula f1 <*> tryEvalFormula f2
    tryEvalFormula _ = Nothing

applySubstOnVar :: Var -> Subst -> Term
applySubstOnVar x sigma = sigma x
