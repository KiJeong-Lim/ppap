module LoL.Core where

import qualified Data.Set as Set

type Level = Integer

type ConstId = Integer

type Hint = String

-- Variables are de Bruijn indices. `Let x t a u` is `let x := t : a in u`.
data Term
    = Prop
    | Type Level
    | Cst ConstId
    | Var Int
    | Pi Hint Term Term
    | Lam Hint Term Term
    | Let Hint Term Term Term
    | App Term Term
    deriving (Show)

-- Binder names are display hints: equality is alpha-equivalence.
instance Eq Term where
    Prop == Prop = True
    Type l1 == Type l2 = l1 == l2
    Cst c1 == Cst c2 = c1 == c2
    Var i1 == Var i2 = i1 == i2
    Pi _ a1 b1 == Pi _ a2 b2 = a1 == a2 && b1 == b2
    Lam _ a1 t1 == Lam _ a2 t2 = a1 == a2 && t1 == t2
    Let _ t1 a1 u1 == Let _ t2 a2 u2 = t1 == t2 && a1 == a2 && u1 == u2
    App t1 u1 == App t2 u2 = t1 == t2 && u1 == u2
    _ == _ = False

apps :: Term -> [Term] -> Term
apps = foldl App

constantsOf :: Term -> Set.Set ConstId
constantsOf term
    = case term of
        Cst c -> Set.singleton c
        Pi _ a b -> Set.union (constantsOf a) (constantsOf b)
        Lam _ a t -> Set.union (constantsOf a) (constantsOf t)
        Let _ t a u -> Set.unions [constantsOf t, constantsOf a, constantsOf u]
        App t u -> Set.union (constantsOf t) (constantsOf u)
        _ -> Set.empty

-- `wellScoped depth t`: every index of `t` is bound by `t` or by one of `depth` enclosing binders.
wellScoped :: Int -> Term -> Bool
wellScoped depth term
    = case term of
        Type l -> l >= 0
        Cst c -> c >= 0
        Var i -> 0 <= i && i < depth
        Pi _ a b -> wellScoped depth a && wellScoped (depth + 1) b
        Lam _ a t -> wellScoped depth a && wellScoped (depth + 1) t
        Let _ t a u -> wellScoped depth t && wellScoped depth a && wellScoped (depth + 1) u
        App t u -> wellScoped depth t && wellScoped depth u
        Prop -> True
