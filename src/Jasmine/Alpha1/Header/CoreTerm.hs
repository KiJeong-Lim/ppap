module Jasmine.Alpha1.Header.CoreTerm where

import Jasmine.Alpha1.Header.Util (LargeId, SmallId, Unique)

type DeBruijn = Int

data PrimTerm
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
    | TmNatLit Integer
    | TmChrLit Char
    | TmPresburgerH
    | TmPresburgerC
    | TmSPY
    deriving (Eq, Ord, Show)

data PrimType
    = TyArrow
    | TyType
    | TyProp
    deriving (Eq, Ord, Show)
