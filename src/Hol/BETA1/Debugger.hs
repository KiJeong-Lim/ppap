module Hol.BETA1.Debugger
    ( NameCache
    , initialCache
    , recordRename
    , toDisplay
    , fromDisplay
    , viewerLookup
    , mergeKeepingNewEntries
    , parseAnonymousLV
    , prettyTerm
    ) where

import qualified Data.Map.Strict as Map
import Hol.BETA1.Header
import Hol.BETA1.Notation (NotationDB, constructViewerWithDB)
import Hol.BETA1.TermNode
import Z.Utils

data NameCache
    = NameCache
    { _toDisplay :: !(Map.Map LogicVar SmallId)
    , _fromDisplay :: !(Map.Map SmallId LogicVar)
    }

initialCache :: NameCache
initialCache = NameCache { _toDisplay = Map.empty, _fromDisplay = Map.empty }

recordRename :: LogicVar -> SmallId -> NameCache -> NameCache
recordRename lv name nc
    = NameCache
    { _toDisplay = Map.insert lv name (evictOldOwner (_toDisplay nc))
    , _fromDisplay = Map.insert name lv (evictOldDisplay (_fromDisplay nc))
    }
    where
        evictOldDisplay m = case Map.lookup lv (_toDisplay nc) of
            Just oldName -> Map.delete oldName m
            Nothing -> m

        evictOldOwner m = case Map.lookup name (_fromDisplay nc) of
            Just oldLv -> Map.delete oldLv m
            Nothing -> m

toDisplay :: LogicVar -> NameCache -> Maybe SmallId
toDisplay lv = Map.lookup lv . _toDisplay

fromDisplay :: SmallId -> NameCache -> Maybe LogicVar
fromDisplay name = Map.lookup name . _fromDisplay

viewerLookup :: NameCache -> LogicVar -> Maybe SmallId
viewerLookup nc lv = toDisplay lv nc

mergeKeepingNewEntries :: NameCache -> NameCache -> NameCache
mergeKeepingNewEntries old new
    = NameCache
    { _toDisplay = Map.union (_toDisplay new) (_toDisplay old)
    , _fromDisplay = Map.union (_fromDisplay new) (_fromDisplay old)
    }

parseAnonymousLV :: String -> Maybe LogicVar
parseAnonymousLV nm = case nm of
    'T' : 'V' : '_' : rest -> mkAnon LV_ty_var rest
    'L' : 'V' : '_' : rest -> mkAnon (\u -> LV_Unique u (DispHint Nothing)) rest
    'V'       : '_' : rest -> mkAnon (\u -> LV_Unique u (DispHint Nothing)) rest
    _ -> Nothing
  where
    mkAnon ctor digits = case reads digits of
        [(n, "")] -> Just (ctor (Unique n))
        _ -> Nothing

prettyTerm :: NotationDB -> NameCache -> TermNode -> ShowS
prettyTerm db cache t = pprint 0 (constructViewerWithDB db (viewerLookup cache) t)
