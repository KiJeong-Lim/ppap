module Jasmine.Alpha1.Header.CoreTerm where

import Jasmine.Alpha1.Header.Util (LargeId, SmallId, Unique)

type DeBruijn = Int

type SuspEnv z = [SuspItem z]

data Tm
    = LO_if
    | LO_true
    | LO_fail
    | LO_cut
    | LO_and
    | LO_or
    | LO_imply
    | LO_forall
    | LO_exists
    | UGuardTm
    | NatLitTm Integer
    | ChrLitTm Char
    | PRESBURGER_H
    | PRESBURGER_C
    | SPY
    deriving (Eq, Ord, Show)

data Ty
    = TyArrow
    | TyType
    deriving (Eq, Ord, Show)

data LogicVar z
    = NamedLV (SmallId)
    | AnonyLV (Unique)
    deriving (Eq, Ord, Show)

data CoreData z
    = DtConstr (SmallId)
    | DtUnique (Unique)
    | PrimOper (z)
    deriving (Eq, Ord, Show)

data CoreTerm z
    = NIdxTm (DeBruijn)
    | NIApTm (CoreTerm z) (CoreTerm Tm)
    | NTApTm (CoreTerm z) (CoreTerm Ty)
    | NAbsTm (CoreTerm z)
    | NConTm (CoreData z)
    | LVarTm (LogicVar z)
    | SupsTm { _susp_body :: CoreTerm z, _ol :: Int, _nl :: Int, _susp_env :: SuspEnv z }
    deriving (Eq, Ord, Show)

data SuspItem z
    = DummyIt (Int)
    | BindsIt (CoreTerm z) (Int)
    deriving (Eq, Ord, Show)
