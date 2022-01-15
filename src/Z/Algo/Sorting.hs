module Z.Algo.Sorting where

import Control.Monad.Trans.Class
import Control.Monad.Trans.State.Strict
import Control.Monad.Trans.Reader
import Data.Functor.Identity
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Z.Algo.Function
import Z.Utils

type IncreasingOrdering element = element -> element -> Bool

type DigraphOf vertex = Map.Map vertex (Set.Set vertex)

data StrongConnectedComponent vertex
    = SCC
        { hasLoop :: !(Bool)
        , myNodes :: !(Set.Set vertex)
        }
    deriving (Eq, Ord, Show)

getTSortedSCCs :: Ord vertex => DigraphOf vertex -> [StrongConnectedComponent vertex]
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
    splitByRel :: Ord node => [node] -> StateT (Set.Set node) (ReaderT (node -> [node]) Identity) [StrongConnectedComponent node]
    splitByRel [] = return []
    splitByRel (cur : nexts) = do
        visteds <- get
        cur_out <- when' (not (cur `Set.member` visteds)) $ do
            scc <- sortByRel [cur]
            return [SCC { hasLoop = cur `elem` scc, myNodes = Set.fromAscList scc }]
        nexts_out <- splitByRel nexts
        return (cur_out ++ nexts_out)
    go :: Ord node => Map.Map node (Set.Set node) -> Identity [StrongConnectedComponent node]
    go given_digraph = do
        let nodes = Set.toAscList (foldr Set.union (Map.keysSet given_digraph) (Map.elems given_digraph))
            froms = maybe [] Set.toAscList . flip Map.lookup given_digraph
            intos = Set.toAscList . Map.keysSet . flip Map.filter given_digraph . Set.member
        (sorted_nodes, _) <- runReaderT (runStateT (sortByRel nodes) Set.empty) froms
        (sorted_sccs, _) <- runReaderT (runStateT (splitByRel sorted_nodes) Set.empty) intos
        return sorted_sccs

sortByMerging :: IncreasingOrdering element -> [element] -> [element]
sortByMerging = go where
    merge :: IncreasingOrdering a -> [a] -> [a] -> [a]
    merge leq (y : ys) (z : zs) = if y `leq` z then y : merge leq ys (z : zs) else z : merge leq (y : ys) zs
    merge leq ys zs = ys ++ zs
    go :: IncreasingOrdering a -> [a] -> [a]
    go leq xs = case length xs `div` 2 of
        0 -> xs
        n -> uncurry (merge leq) . (go leq <^> go leq) $ (splitAt n xs)
