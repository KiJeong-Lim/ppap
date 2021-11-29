module Jasmine.Alpha1.Header.TermNode where

import Jasmine.Alpha1.Header.Util (LargeId, SmallId, Unique)
import Z.Algo.Function
import Z.Utils

type SmallNat = Int

type DeBruijn = SmallNat

type SuspEnv = [SuspItem]

type Nat_ol = SmallNat

type Nat_nl = SmallNat

data Primitives
    = TmLoIf
    | TmLoTrue
    | TmLoFail
    | TmLoCut
    | TmLoAnd
    | TmLoOr
    | TmLoImply
    | TmLoForall
    | TmLoExists
    | TmWcard
    | TmGuard
    | TmSucc
    | TmNatLit MyNat
    | TmChrLit Char
    | TmPresburgerH
    | TmPresburgerC
    | SPY
    | TyBang
    | TyArrow
    | TyType
    | TyProp
    deriving (Eq, Ord, Show)

data AtomNode
    = Uniq Bool Unique
    | Prim Primitives
    deriving (Eq, Ord, Show)

data TermNode
    = NIdx DeBruijn
    | NApp TermNode TermNode
    | NLam TermNode
    | Susp TermNode Nat_ol Nat_nl SuspEnv
    | Atom AtomNode
    deriving (Eq, Ord, Show)

data SuspItem
    = Dummy SmallNat
    | Binds TermNode SmallNat
    deriving (Eq, Ord, Show)

fromPrim :: Primitives -> TermNode
fromPrim = callWithStrictArg (Atom . Prim)

mkNatL :: MyNat -> TermNode
mkNatL = callWithStrictArg (Atom . Prim . TmNatLit)

mkChrL :: Char -> TermNode
mkChrL = callWithStrictArg (Atom . Prim . TmChrLit)

mkNIdx :: DeBruijn -> TermNode
mkNIdx i = NIdx $! i

mkNApp :: TermNode -> TermNode -> TermNode
mkNApp (Atom (Prim (TmSucc))) (Atom (Prim (TmNatLit n))) = mkNatL $! succ n
mkNApp t1 t2 = NApp t1 $! t2

mkNLam :: TermNode -> TermNode
mkNLam t1 = NLam $! t1

mkAtom :: AtomNode -> TermNode
mkAtom = callWithStrictArg Atom

mkSusp :: TermNode -> Nat_ol -> Nat_nl -> SuspEnv -> TermNode
mkSusp t 0 0 [] = t
mkSusp t ol nl env = callWithStrictArg Susp t ol nl env

mkBinds :: TermNode -> SmallNat -> SuspItem
mkBinds t l = Binds t $! l

mkDummy :: SmallNat -> SuspItem
mkDummy l = Dummy $! l
