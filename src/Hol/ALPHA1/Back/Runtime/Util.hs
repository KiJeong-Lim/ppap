module Hol.ALPHA1.Back.Runtime.Util where

import Hol.ALPHA1.Back.Base.Constant
import Hol.ALPHA1.Back.Base.Labeling
import Hol.ALPHA1.Back.Base.TermNode
import Hol.ALPHA1.Back.Base.TermNode.Util
import Hol.ALPHA1.Back.Base.VarBinding
import Hol.ALPHA1.Back.HOPU.Util
import Hol.ALPHA1.Back.Runtime.Arith
import Hol.ALPHA1.Front.Header
import Control.Monad.Trans.Except
import Control.Monad.Trans.State.Strict
import Data.IORef
import qualified Data.List as List
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Y.Base

type Fact = TermNode

type Goal = TermNode

type Stack = [(Context, [Cell])]

type Satisfied = Bool

type RunMore = Bool

type CallId = Unique

type Debugging = Bool

data KernelErr
    = BadGoalGiven TermNode
    | BadFactGiven TermNode
    | ArithmeticFailure ArithmeticError
    | QuitRequested
    deriving ()

data Clause
    = Clause
        { _ClauseBody :: Fact
        , _ClauseHead :: Maybe Constant
        }
    deriving ()

data Cell
    = Cell
        { _LocalFacts :: [Clause]
        , _ScopeLevel :: ScopeLevel
        , _WantedGoal :: Goal
        , _CellCallId :: CallId
        }
    | MatchClause
        { _LocalFacts :: [Clause]
        , _ScopeLevel :: ScopeLevel
        , _WantedGoal :: Goal
        , _CellCallId :: CallId
        , _CandidateFact :: Fact
        }
    deriving ()

data Context
    = Context
        { _TotalVarBinding :: VarBinding
        , _CurrentLabeling :: Labeling
        , _LeftConstraints :: [Disagreement]
        , _ContextThreadId :: CallId
        , _debuggindModeOn :: IORef Debugging
        }
    deriving ()

data RuntimeEnv
    = RuntimeEnv
        { _PutStr :: Context -> String -> IO Bool
        , _Answer :: Context -> IO RunMore
        }
    deriving ()

instance ZonkLVar Clause where
    zonkLVar theta (Clause fact predicate) = Clause (applyBinding theta fact) predicate

instance ZonkLVar Cell where
    zonkLVar theta (Cell facts level goal call_id) = Cell (zonkLVar theta facts) level (applyBinding theta goal) call_id
    zonkLVar theta (MatchClause facts level goal call_id fact) = MatchClause (zonkLVar theta facts) level (applyBinding theta goal) call_id (applyBinding theta fact)

mkClause :: Fact -> Clause
mkClause fact = Clause { _ClauseBody = fact, _ClauseHead = headPredicate fact }

headPredicate :: Fact -> Maybe Constant
headPredicate fact = case unfoldlNApp (rewrite HNF fact) of
    (NCon (DC (DC_LO LO_ty_pi)), [body]) -> under body
    (NCon (DC (DC_LO LO_pi)), [body]) -> under body
    (NCon (DC (DC_LO LO_if)), [conclusion, premise]) -> headPredicate conclusion
    (NCon (DC (DC_LO logical_operator)), args) -> Nothing
    (NCon predicate, args) -> Just predicate
    _ -> Nothing
    where
        under :: TermNode -> Maybe Constant
        under body = case rewrite HNF body of
            NAbs body' -> headPredicate body'
            _ -> Nothing

mkCell :: [Clause] -> ScopeLevel -> Goal -> CallId -> Cell
mkCell facts level goal call_id = goal `seq` Cell { _LocalFacts = facts, _ScopeLevel = level, _WantedGoal = goal, _CellCallId = call_id }

showStackItem :: Set.Set LogicVar -> Indentation -> (Context, [Cell]) -> ShowS
showStackItem fvs space (ctx, cells) = strcat
    [ pindent space . strstr "+ progressings = " . plist (space + 4) [ strstr "?- " . shows (_WantedGoal cell) . strstr " # call_id = " . shows (_CellCallId cell) | cell <- cells ] . nl
    , pindent space . strstr "+ context = Context" . nl
    , pindent (space + 4) . strstr "{ " . strstr "_scope_env = " . plist (space + 8) ([ shows (mkNCon c) . strstr " *--- " . shows level | (c, level) <- Map.toList (_ConLabel (_CurrentLabeling ctx)) ] ++ [ shows (mkLVar v) . strstr " *--- " . shows level | (v, level) <- Map.toList (_VarLabel (_CurrentLabeling ctx)), v `Set.member` fvs || not (v `Set.member` Map.keysSet (unVarBinding (_TotalVarBinding ctx))) ]) . nl
    , pindent (space + 4) . strstr ", " . strstr "_substitution = " . plist (space + 8) [ shows (LVar v) . strstr " |--> " . shows (resolveBinding (_TotalVarBinding ctx) t) | (v, t) <- Map.toList (unVarBinding (_TotalVarBinding ctx)), v `Set.member` fvs ] . nl
    , pindent (space + 4) . strstr ", " . strstr "_constraints = " . plist (space + 8) [ shows constraint | constraint <- _LeftConstraints ctx ] . nl
    , pindent (space + 4) . strstr ", " . strstr "_thread_id = " . shows (_ContextThreadId ctx) . nl
    , pindent (space + 4) . strstr "}" . nl
    ]

showsCurrentState :: Set.Set LogicVar -> Context -> [Cell] -> Stack -> ShowS
showsCurrentState fvs ctx cells stack = strcat
    [ strstr "--------------------------------" . nl 
    , strstr "* The top of the current stack is:" . nl
    , showStackItem fvs 4 (ctx, cells) . nl
    , strstr "* The rest of the current stack is:" . nl
    , strcat
        [ strcat
            [ pindent 0 . strstr "- (#" . shows i . strstr ")" . nl
            , showStackItem fvs 4 item . nl
            ]
        | (i, item) <- zip [1, 2 .. length stack] stack
        ]
    , strstr "--------------------------------" . nl
    ]
