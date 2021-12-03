module Jasmine.Alpha1.Header.TermNode where

import qualified Data.List as List
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Jasmine.Alpha1.Header.Util
import Z.Algo.Function
import Z.Utils

type SmallNat = Int

type DeBruijn = SmallNat

type SuspEnv = [SuspItem]

type Nat_ol = SmallNat

type Nat_nl = SmallNat

type ScopeLevel = SmallNat

type DoesRepresentType = Bool

data LogicVar
    = TyLVar Unique
    | TmLVar Unique
    deriving (Eq, Ord, Show)

data Constructor
    = DataConstr DataConstructor
    | TypeConstr TypeConstructor
    deriving (Eq, Ord, Show)

data Primitives
    = LogicOper_if
    | LogicOper_all
    | LogicOper_some
    | LogicOper_and
    | LogicOper_or
    | LogicOper_imply
    | LogicOper_cut
    | LogicOper_fail
    | LogicOper_true
    | LogicOper_type_abs
    | INTERRUPT
    | WILD_CARD
    deriving (Eq, Ord, Show)

data TermNode
    = NIdx DeBruijn
    | NApp TermNode TermNode
    | NLam TermNode
    | NFix TermNode
    | Susp TermNode Nat_ol Nat_nl SuspEnv
-- $Susp t ol nl env$ is a suspension of evaluation, where
-- $t$ is the evaluatee;
-- $ol$ is the length of $env$;
-- $nl$ counts how many binders we have encountered;
-- $env$ is the context of variables, which are bound by binders we have encountered.
    | LVar LogicVar
    | NCon Constructor
    | Prim Primitives
    deriving (Eq, Ord, Show)

data SuspItem
    = Dummy SmallNat
-- $Dummy l$ refers the variable bound by the $l$-th binder, which has no evaluation reference.
    | Binds TermNode SmallNat
-- $Binds t l$ refers the variable bound by the $l$-th binder, whose evaluation reference is $t$.
    deriving (Eq, Ord, Show)

class Constructible c where
    mkNCon :: c -> TermNode

instance Constructible (DataConstructor) where
    mkNCon = callWithStrictArg (NCon . DataConstr)

instance Constructible (TypeConstructor) where
    mkNCon = callWithStrictArg (NCon . TypeConstr)

instance Constructible (Constructor) where
    mkNCon c = NCon $! c

flexTVar :: Unique -> TermNode
flexTVar = callWithStrictArg (LVar . TyLVar)

flexIVar :: Unique -> TermNode
flexIVar = callWithStrictArg (LVar . TmLVar)

viewFlex :: LogicVar -> (Unique, DoesRepresentType)
viewFlex (TyLVar v) = (v, True)
viewFlex (TmLVar v) = (v, False)

viewDCon :: Constructor -> Maybe DataConstructor
viewDCon (DataConstr c) = Just c
viewDCon _ = Nothing

viewTCon :: Constructor -> Maybe TypeConstructor
viewTCon (TypeConstr c) = Just c
viewTCon _ = Nothing

fromPrim :: Primitives -> TermNode
fromPrim = callWithStrictArg Prim

viewPrim :: TermNode -> Maybe Primitives
viewPrim (Prim prim_op) = Just prim_op
viewPrim _ = Nothing

mkLVar :: LogicVar -> TermNode
mkLVar = callWithStrictArg LVar

mkNIdx :: DeBruijn -> TermNode
mkNIdx i = NIdx $! i

mkNApp :: TermNode -> TermNode -> TermNode
mkNApp (NCon (DataConstr (DC_SuccOf))) (NCon (DataConstr (DC_NatLit n))) = callWithStrictArg (mkNCon . DC_NatLit) (succ n)
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
