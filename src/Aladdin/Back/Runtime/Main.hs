module Aladdin.Back.Runtime.Main where

import Aladdin.Back.Base.Labeling
import Aladdin.Back.Base.TermNode
import Aladdin.Back.Base.TermNode.Util
import Aladdin.Back.Base.VarBinding
import Aladdin.Back.Runtime.Transition
import Aladdin.Back.Runtime.Util
import Aladdin.Front.Header
import Control.Monad.IO.Class
import Control.Monad.Trans.Except
import Control.Monad.Trans.State.Strict
import Data.IORef
import qualified Data.List as List
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set

execRuntime :: RuntimeEnv -> IORef Bool -> [Fact] -> Goal -> ExceptT KernelErr (UniqueGenT IO) Satisfied
execRuntime env isDebugging program query = do
    call_id <- getNewUnique
    let initialContext = Context { _TotalVarBinding = mempty, _CurrentLabeling = Labeling { _ConLabel = Map.empty, _VarLabel = Map.fromSet (const 0) (getFreeLVs query) }, _LeftConstraints = [], _ContextThreadId = call_id, _debuggindModeOn = isDebugging }
    runTransition env (getFreeLVs query) [(initialContext, [Cell { _GivenFacts = program, _ScopeLevel = 0, _WantedGoal = query, _CellCallId = call_id }])]
