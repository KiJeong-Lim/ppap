module Jasmine.Alpha1.Header.TermNode where

import Jasmine.Alpha1.Header.Util (LargeId, SmallId, Identifier, Unique)
import Z.Utils

type DeBruijn = Int

type SuspEnv = [SuspItem]

type Nat_ol = Int

type Nat_nl = Int

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
    | TmNatLit Integer
    | TmChrLit Char
    | TmPresburgerH
    | TmPresburgerC
    | SPY
    | TyArrow
    | TyType
    | TyProp
    deriving (Eq, Ord, Show)

data AtomNode
    = TempAN Bool Unique
    | NameAN Bool Identifier
    | PrimAN Primitives
    deriving (Eq, Ord, Show)

data TermNode
    = NIdx DeBruijn
    | NApp TermNode TermNode
    | NLam TermNode
    | Susp TermNode Nat_ol Nat_nl SuspEnv
    | Atom AtomNode
    deriving (Eq, Ord, Show)

data SuspItem
    = Dummy Int
    | Binds TermNode Int
    deriving (Eq, Ord, Show)

fromPrim :: Primitives -> TermNode
fromPrim = callWithStrictArg (Atom . PrimAN)

mkNatL :: Integer -> TermNode
mkNatL = callWithStrictArg (Atom . PrimAN . TmNatLit)

mkChrL :: Char -> TermNode
mkChrL = callWithStrictArg (Atom . PrimAN . TmChrLit)

mkNIdx :: DeBruijn -> TermNode
mkNIdx i = callWithStrictArg NIdx i

mkNApp :: TermNode -> TermNode -> TermNode
mkNApp (Atom (PrimAN (TmSucc))) (Atom (PrimAN (TmNatLit n))) = callWithStrictArg mkNatL (succ n)
mkNApp t1 t2 = callWithStrictArg NApp t1 t2

mkNLam :: TermNode -> TermNode
mkNLam t1 = callWithStrictArg NLam t1

mkSusp :: TermNode -> Nat_ol -> Nat_nl -> SuspEnv -> TermNode
mkSusp t 0 0 [] = t
mkSusp t ol nl env = callWithStrictArg Susp t ol nl env

mkBinds :: TermNode -> Int -> SuspItem
mkBinds t l = Binds t l

mkDummy :: Int -> SuspItem
mkDummy l = Dummy l

isRigid :: AtomNode -> Bool
isRigid (TempAN is_rigid _) = is_rigid
isRigid (NameAN is_rigid _) = is_rigid
isRigid (PrimAN _) = True

unfoldlNApp :: TermNode -> (TermNode, [TermNode])
unfoldlNApp = flip go [] where
    go :: TermNode -> [TermNode] -> (TermNode, [TermNode])
    go (Atom (PrimAN (TmNatLit n))) ts = if n == 0 then (mkNatL 0, ts) else (fromPrim TmSucc, mkNatL (pred n) : ts)
    go (NApp t1 t2) ts = go t1 (t2 : ts)
    go t ts = (t, ts)
