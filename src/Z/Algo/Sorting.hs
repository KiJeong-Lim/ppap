module Z.Algo.Sorting where

import Control.Monad.Trans.Class
import Control.Monad.Trans.State.Strict
import Control.Monad.Trans.Reader
import Data.Functor.Identity
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Z.Algo.Function
import Z.Utils

type IsCircular = Bool

type IncreasingOrdering a = a -> a -> Bool

type DigraphOf vertices = Map.Map vertices (Set.Set vertices)

getTSortedSCCs :: Ord node => DigraphOf node -> [(IsCircular, Set.Set node)]
getTSortedSCCs = runIdentity . go where
    when' :: (Functor m, Monoid a) => Bool -> m a -> m a
    when' cond = if cond then id else fmap (const mempty)
    sortByRel :: Ord node => [node] -> StateT (Set.Set node) (ReaderT (node -> [node]) Identity) [node]
    sortByRel [] = return []
    sortByRel (cur : nexts) = do
        visteds <- get
        ges <- when' (not (cur `Set.member` visteds)) $ do
            put (Set.insert cur visteds)
            rel <- lift ask
            gts <- sortByRel (rel cur)
            return (cur : gts)
        lts <- sortByRel nexts
        return (lts ++ ges)
    splitByRel :: Ord node => [node] -> StateT (Set.Set node) (ReaderT (node -> [node]) Identity) [(IsCircular, Set.Set node)]
    splitByRel [] = return []
    splitByRel (cur : nexts) = do
        visteds <- get
        cur_res <- when' (not (cur `Set.member` visteds)) $ do
            ges <- sortByRel [cur]
            return (one (cur `elem` ges, Set.fromAscList ges))
        next_res <- splitByRel nexts
        return (cur_res ++ next_res)
    go :: Ord node => Map.Map node (Set.Set node) -> Identity [(IsCircular, Set.Set node)]
    go given_digraph = do
        let nodes = Set.toAscList (foldr Set.union (Map.keysSet given_digraph) (Map.elems given_digraph))
            froms = maybe [] Set.toAscList . flip Map.lookup given_digraph
            intos = Set.toAscList . Map.keysSet . flip Map.filter given_digraph . Set.member
        (sortedVertices, _) <- runReaderT (runStateT (sortByRel nodes) Set.empty) froms
        (sortedSCCs, _) <- runReaderT (runStateT (splitByRel nodes) Set.empty) intos
        return sortedSCCs

sortByMerging :: IncreasingOrdering a -> [a] -> [a]
sortByMerging = go where
    go :: IncreasingOrdering a -> [a] -> [a]
    go leq xs = case length xs `div` 2 of
        0 -> xs
        n -> uncurry (merge leq) . (go leq <^> go leq) $ (splitAt n xs)
    merge :: IncreasingOrdering a -> [a] -> [a] -> [a]
    merge leq (y : ys) (z : zs) = if y `leq` z then y : merge leq ys (z : zs) else z : merge leq (y : ys) zs
    merge leq ys zs = ys ++ zs
