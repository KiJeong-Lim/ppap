module Z.Algo.Sorting where

import Control.Monad.Trans.Class
import Control.Monad.Trans.State.Strict
import Control.Monad.Trans.Reader
import Data.Functor.Identity
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set

type IsCircular = Bool

type IncreasingOrdering a = a -> a -> Bool

getTSortedSCCs :: Ord node => Map.Map node (Set.Set node) -> [(IsCircular, Set.Set node)]
getTSortedSCCs = runIdentity . go where
    whenMaybe :: Applicative m => Bool -> m a -> m (Maybe a)
    whenMaybe cond m = if cond then pure Just <*> m else pure Nothing
    sortByRel :: Ord node => [node] -> StateT (Set.Set node) (ReaderT (node -> [node]) Identity) [node]
    sortByRel [] = return []
    sortByRel (cur : nexts) = do
        visteds <- get
        maybe_ges <- whenMaybe (not (cur `Set.member` visteds)) $ do
            put (Set.insert cur visteds)
            rel <- lift ask
            gts <- sortByRel (rel cur)
            return (cur : gts)
        lts <- sortByRel nexts
        return (maybe lts (\ges -> lts ++ ges) maybe_ges)
    splitByRel :: Ord node => [node] -> StateT (Set.Set node) (ReaderT (node -> [node]) Identity) [(IsCircular, Set.Set node)]
    splitByRel [] = return []
    splitByRel (cur : nexts) = do
        visteds <- get
        maybe_ges <- whenMaybe (not (cur `Set.member` visteds)) (sortByRel [cur])
        sets <- splitByRel nexts
        return (maybe sets (\ges -> (cur `elem` ges, Set.fromAscList ges) : sets) maybe_ges)
    go :: Ord node => Map.Map node (Set.Set node) -> Identity [(IsCircular, Set.Set node)]
    go getDigraph = do
        let getVertices = Set.toAscList (Map.keysSet getDigraph)
            getOuts node = Set.toAscList (maybe (error "In `Z.Algo.Sorting.getTSortedSCCs':\n  an-element-is-out-of-domain.") id (Map.lookup node getDigraph))
            getIns node = [ node' | (node', nodes) <- Map.toAscList getDigraph, node `Set.member` nodes ]
        (sortedVertices, _) <- runReaderT (runStateT (sortByRel getVertices) Set.empty) getOuts
        (sortedSCCs, _) <- runReaderT (runStateT (splitByRel getVertices) Set.empty) getIns
        return sortedSCCs

sortByMerging :: IncreasingOrdering a -> [a] -> [a]
sortByMerging = go where
    go :: IncreasingOrdering a -> [a] -> [a]
    go leq xs
        | n > 0 = case splitAt n xs of
            (ys, zs) -> merge leq (go leq ys) (go leq zs)
        | otherwise = xs
        where
            n :: Int
            n = length xs `div` 2
    merge :: IncreasingOrdering a -> [a] -> [a] -> [a]
    merge leq (y : ys) (z : zs)
        | y `leq` z = y : merge leq ys (z : zs)
        | otherwise = z : merge leq (y : ys) zs
    merge leq ys zs = ys ++ zs
