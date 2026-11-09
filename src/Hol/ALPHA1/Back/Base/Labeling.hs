module Hol.ALPHA1.Back.Base.Labeling where

import Hol.ALPHA1.Back.Base.Constant
import Hol.ALPHA1.Back.Base.TermNode
import Hol.ALPHA1.Back.Base.TermNode.Util
import Hol.ALPHA1.Back.Base.VarBinding
import Hol.ALPHA1.Front.Header
import Data.Foldable
import qualified Data.List as List
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set

type ScopeLevel = Int

data Labeling
    = Labeling
        { _ConLabel :: Map.Map Constant ScopeLevel
        , _VarLabel :: Map.Map LogicVar ScopeLevel
        }
    deriving ()

class Labelable atom where
    enrollLabel :: atom -> ScopeLevel -> Labeling -> Labeling
    updateLabel :: atom -> ScopeLevel -> Labeling -> Labeling
    lookupLabel :: atom -> Labeling -> ScopeLevel

instance Labelable Constant where
    enrollLabel atom level labeling = labeling { _ConLabel = Map.insert atom level (_ConLabel labeling) }
    updateLabel atom level labeling = labeling { _ConLabel = Map.update (const (Just level)) atom (_ConLabel labeling) }
    lookupLabel (DC data_constructor) = maybe (theDefaultLevel data_constructor) id . Map.lookup (DC data_constructor) . _ConLabel
    lookupLabel (TC type_constructor) = const 0

instance Labelable LogicVar where
    enrollLabel atom level labeling = labeling { _VarLabel = Map.insert atom level (_VarLabel labeling) }
    updateLabel atom level labeling = labeling { _VarLabel = Map.update (const (Just level)) atom (_VarLabel labeling) }
    lookupLabel atom = maybe maxBound id . Map.lookup atom . _VarLabel

instance ZonkLVar Labeling where
    zonkLVar subst labeling = labeling { _VarLabel = Map.foldlWithKey' lower varlabel (unVarBinding subst) } where
        varlabel :: Map.Map LogicVar ScopeLevel
        varlabel = _VarLabel labeling
        lower :: Map.Map LogicVar ScopeLevel -> LogicVar -> TermNode -> Map.Map LogicVar ScopeLevel
        lower acc v' t' = case Map.lookup v' varlabel of
            Nothing -> acc
            Just level' -> foldl' (\acc' v -> Map.adjust (min level') v acc') acc (Set.toList (getFreeLVs t'))

theDefaultLevel :: DataConstructor -> ScopeLevel
theDefaultLevel (DC_Unique uni) = maxBound
theDefaultLevel _ = 0
