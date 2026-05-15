module Hol.BETA1.Debugger
    ( NameCache
    , initialCache
    , recordRename
    , toDisplay
    , fromDisplay
    , viewerLookup
    ) where

import qualified Data.Map.Strict as Map
import Hol.BETA1.Header
import Hol.BETA1.TermNode

-- =============================================================
-- §3.5 / §4.4.4 — Display-name cache
-- =============================================================
--
-- The cache lives in `Debugger.hs`, not in `Runtime.hs`. The runtime
-- kernel is correct without any awareness of display naming; the
-- cache is concerned only with UX continuity for an interactive
-- session. Keeping it here preserves the property that `Runtime.hs`
-- can be re-used (by `LoL` or by future versions) without dragging
-- in any string-naming policy.
--
-- The cache survives across stepping, across `:assign` commits, and
-- across `:assign` aborts (the rollback of §3.2.3 does *not* discard
-- cache entries — that would re-confuse the user about variable
-- naming). The cache is discarded only when the debug session ends.

data NameCache = NameCache
    { _toDisplay :: !(Map.Map LogicVar SmallId)
    , _fromDisplay :: !(Map.Map SmallId LogicVar)
    }

initialCache :: NameCache
initialCache = NameCache
    { _toDisplay = Map.empty
    , _fromDisplay = Map.empty
    }

-- Record a rename. If `lv` already had a display name, the previous
-- (display -> lv) binding is removed so that the cache stays
-- bidirectional. If `name` was previously used for a different
-- LogicVar, that mapping is overwritten on the forward side too —
-- the most recent assignment wins.
recordRename :: LogicVar -> SmallId -> NameCache -> NameCache
recordRename lv name nc =
    let -- evict the previous display name (if any) on the reverse map
        evictOldDisplay m = case Map.lookup lv (_toDisplay nc) of
            Just oldName -> Map.delete oldName m
            Nothing -> m
        -- evict the previous owner of `name` on the forward map
        evictOldOwner m = case Map.lookup name (_fromDisplay nc) of
            Just oldLv -> Map.delete oldLv m
            Nothing -> m
    in NameCache
        { _toDisplay = Map.insert lv name (evictOldOwner (_toDisplay nc))
        , _fromDisplay = Map.insert name lv (evictOldDisplay (_fromDisplay nc))
        }

toDisplay :: LogicVar -> NameCache -> Maybe SmallId
toDisplay lv = Map.lookup lv . _toDisplay

fromDisplay :: SmallId -> NameCache -> Maybe LogicVar
fromDisplay name = Map.lookup name . _fromDisplay

-- Argument shape required by `TermNode.constructViewerWith`. The viewer
-- needs a pure `LogicVar -> Maybe SmallId` lookup; this is just `toDisplay`
-- with the arguments flipped to match.
viewerLookup :: NameCache -> LogicVar -> Maybe SmallId
viewerLookup nc lv = toDisplay lv nc
