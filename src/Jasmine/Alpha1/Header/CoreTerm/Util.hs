module Jasmine.Alpha1.Header.CoreTerm.Util where

import Jasmine.Alpha1.Header.CoreTerm

data ReduceOption
    = WHNF
    | HNF
    | HF
    deriving (Eq)
