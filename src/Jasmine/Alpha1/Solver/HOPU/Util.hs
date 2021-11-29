module Jasmine.Alpha1.Solver.HOPU.Util where

import Control.Monad
import Control.Monad.Trans.Class
import Control.Monad.Trans.Except
import Control.Monad.Trans.Reader
import Control.Monad.Trans.State.Strict
import Data.Functor.Identity
import qualified Data.List as List
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Jasmine.Alpha1.Header.Export
import Z.Algo.Function
import Z.Utils

data Cause
    = ByRew
    | BySpy
    | GUARD
    | ByERR
    | OCCUR
    | ByNaP
    | NotFR
    deriving (Eq, Ord, Show)

data Problem
    = TermNode :==: TermNode
    | Delayed Cause TermNode TermNode
    deriving (Eq, Ord, Show)

isConstr :: AtomNode -> Bool
isConstr (Uniq is_constr _) = is_constr
isConstr (Prim pr) = pr /= TmWcard && pr /= SPY

isRigid :: TermNode -> Bool
isRigid (Atom a) = isConstr a
isRigid (NIdx i) = True
isRigid _ = False

getLVar :: TermNode -> Maybe Unique
getLVar (Atom (Uniq False x)) = Just x
getLVar _ = Nothing

areAllDistinct :: Eq a => [a] -> Bool
areAllDistinct [] = True
areAllDistinct (x : xs) = not (x `elem` xs) && areAllDistinct xs

isPattern :: [TermNode] -> Bool
isPattern ts = and
    [ areAllDistinct ts
    , all isRigid ts
    ]

getScopeLevel :: AtomEnv -> AtomNode -> ScopeLevel
getScopeLevel env (Prim pr) = if pr == TmWcard || pr == SPY then maxBound else 0
getScopeLevel env (Uniq is_constr uni) = maybe maxBound _scope_lv (Map.lookup uni env)

isPatternWRT :: [TermNode] -> AtomNode -> ReaderT AtomEnv Identity Bool
isPatternWRT ts v = ReaderT $ \env -> return (isPattern ts && and [ getScopeLevel env v < getScopeLevel env c | Atom c <- ts ])

down :: [TermNode] -> [TermNode] -> Maybe [TermNode]
params `down` args
    | isPattern params && isPattern args = return selecteds
    | otherwise = fail ""
    where
        n :: Int
        n = length args - 1
        selecteds :: [TermNode]
        selecteds = do
            p <- params
            i <- maybe [] one (p `List.elemIndex` args)
            return (mkNIdx (n - i))

up :: [TermNode] -> AtomNode -> ReaderT AtomEnv Maybe [TermNode]
args `up` v
    | isPattern args = ReaderT $ \env -> return [ mkAtom c | Atom c <- args, getScopeLevel env v >= getScopeLevel env c ]
    | otherwise = fail "" 
