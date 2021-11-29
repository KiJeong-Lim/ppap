module Jasmine.Alpha1.Header.TermNode where

import Jasmine.Alpha1.Header.Util (LargeId, SmallId, Unique)
import Z.Algo.Function
import Z.Utils

type SmallNat = Int

type DeBruijn = SmallNat

type SuspEnv = [SuspItem]

type Nat_ol = SmallNat

type Nat_nl = SmallNat

data LogicVar
    = LogicVar
    deriving (Eq, Ord, Show)

data Constructor
    = Constructor
    deriving (Eq, Ord, Show)

data Primitives
    = Primitives
    deriving (Eq, Ord, Show)

data TermNode
    = NIdx DeBruijn
    | NApp TermNode TermNode
    | NLam TermNode
    | Susp TermNode Nat_ol Nat_nl SuspEnv
    | LVar LogicVar
    | NCon Constructor
    | Prim Primitives
    deriving (Eq, Ord, Show)

data SuspItem
    = Dummy SmallNat
    | Binds TermNode SmallNat
    deriving (Eq, Ord, Show)

mkLVar :: LogicVar -> TermNode
mkLVar = callWithStrictArg LVar

mkNCon :: Constructor -> TermNode
mkNCon = callWithStrictArg NCon

mkNIdx :: DeBruijn -> TermNode
mkNIdx i = NIdx $! i

mkNApp :: TermNode -> TermNode -> TermNode
mkNApp t1 t2 = NApp t1 $! t2

mkNLam :: TermNode -> TermNode
mkNLam t1 = NLam $! t1

mkSusp :: TermNode -> Nat_ol -> Nat_nl -> SuspEnv -> TermNode
mkSusp t 0 0 [] = t
mkSusp t ol nl env = callWithStrictArg Susp t ol nl env

mkBinds :: TermNode -> SmallNat -> SuspItem
mkBinds t l = Binds t $! l

mkDummy :: SmallNat -> SuspItem
mkDummy l = Dummy $! l
