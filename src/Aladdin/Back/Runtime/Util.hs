module Aladdin.Back.Runtime.Util where

import Aladdin.Back.Base.Labeling
import Aladdin.Back.Base.TermNode
import Aladdin.Back.Base.VarBinding
import Aladdin.Back.HOPU.Util
import Aladdin.Front.Header
import Control.Monad.Trans.Except
import Control.Monad.Trans.State.Strict
import qualified Data.List as List
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Y.Base

type Fact = TermNode

type Goal = TermNode

type Stack = [(Context, [Cell])]

type Satisfied = Bool

type RunMore = Bool

type CallDepth = Int

data KernelErr
    = BadGoalGiven TermNode
    | BadFactGiven TermNode
    deriving ()

data Cell
    = Cell
        { _GivenFacts :: [Fact]
        , _ScopeLevel :: ScopeLevel
        , _WantedGoal :: Goal
        , _call_depth :: CallDepth
        }
    deriving ()

data Context
    = Context
        { _TotalVarBinding :: VarBinding
        , _CurrentLabeling :: Labeling
        , _LeftConstraints :: [Disagreement]
        }
    deriving ()

data RuntimeEnv
    = RuntimeEnv
        { _PutStr :: String -> IO ()
        , _Answer :: Context -> IO RunMore
        }
    deriving ()

instance ZonkLVar Cell where
    zonkLVar theta (Cell facts level goal depth) = Cell (applyBinding theta facts) level (applyBinding theta goal) depth

showStackItem :: Set.Set LogicVar -> Indentation -> (Context, [Cell]) -> ShowS
showStackItem fvs space (ctx, cells) = strcat
    [ pindent space . strstr "- progressings = " . plist (space + 4) [ strstr "?- " . shows goal . strstr " <--------- _call_depth = " . shows depth | Cell facts level goal depth <- cells ] . nl
    , pindent space . strstr "- context = Context" . nl
    , pindent (space + 4) . strstr "{ " . strstr "_scope_env = " . plist (space + 8) ([ strstr "`" . shows (mkNCon c) . strstr "\' *--- " . shows level | (c, level) <- Map.toList (_ConLabel (_CurrentLabeling ctx)) ] ++ [ strstr "`" . shows (mkLVar v) . strstr "\' *--- " . shows level | (v, level) <- Map.toList (_VarLabel (_CurrentLabeling ctx)), v `Set.member` fvs || not (v `Set.member` Map.keysSet (unVarBinding (_TotalVarBinding ctx))) ]) . nl
    , pindent (space + 4) . strstr ", " . strstr "_substitution = " . plist (space + 8) [ strstr "`" . shows (LVar v) . strstr "\' |--> " . shows t | (v, t) <- Map.toList (unVarBinding (_TotalVarBinding ctx)), v `Set.member` fvs ] . nl
    , pindent (space + 4) . strstr ", " . strstr "_constraints = " . plist (space + 8) [ shows constraint | constraint <- _LeftConstraints ctx ] . nl
    , pindent (space + 4) . strstr "} " . nl
    ]

showsCurrentState :: Set.Set LogicVar -> Context -> [Cell] -> Stack -> ShowS
showsCurrentState fvs ctx cells stack = strcat
    [ strstr "-------------------------"
    , strstr "* The top of the current stack is:" . nl
    , showStackItem fvs 4 (ctx, cells) . nl
    , strstr "* The rest of the current stack is:" . nl
    , strcat
        [ strcat
            [ pindent 2 . strstr "+ #[" . shows i . strstr "]:" . nl
            , showStackItem fvs 4 item . nl
            ]
        | (i, item) <- zip [1, 2 .. length stack] stack
        ]
    , strstr "--------------------------------" . nl
    ]

mkCell :: [Fact] -> ScopeLevel -> Goal -> CallDepth -> Cell
mkCell facts level goal depth = goal `seq` Cell { _GivenFacts = facts, _ScopeLevel = level, _WantedGoal = goal, _call_depth = depth }
