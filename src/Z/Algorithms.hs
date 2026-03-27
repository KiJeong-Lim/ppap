{-# LANGUAGE ScopedTypeVariables #-}
module Z.Algorithms where

import Control.Monad
import Control.Monad.Trans.Class
import Control.Monad.Trans.Except
import Control.Monad.Trans.State.Strict
import Control.Monad.Trans.Reader
import qualified Data.Foldable as Foldable
import qualified Data.Function as Function
import qualified Data.Functor.Identity as Identity
import qualified Data.Map.Strict as Map
import qualified Data.Maybe as Maybe
import qualified Data.Set as Set
import GHC.Stack
import Z.Utils

infixr 3 />

infixl 1 <^>

type PositiveInteger = Integer

type MyNat = Integer

type ErrMsgM = Either String

type IncreasingOrdering element = element -> element -> Bool

type DigraphOf vertex = Map.Map vertex (Set.Set vertex)

data StrongConnectedComponent vertex
    = SCC
        { hasLoop :: !(Bool)
        , myNodes :: !(Set.Set vertex)
        }
    deriving (Eq, Ord, Show)

class Failable a where
    alt :: a -> a -> a

class Failable a => FailableZero a where
    nil :: a

(/>) :: Failable a => a -> a -> a
x /> y = alt x y

takeFirstOf :: FailableZero b => (a -> b) -> [a] -> b
takeFirstOf f = foldr alt nil . map f

fromJust :: HasCallStack => Maybe a -> a
fromJust = Maybe.fromJust

fromErrMsgM :: HasCallStack => ErrMsgM a -> a
fromErrMsgM = either error id

addErrMsg :: String -> Maybe a -> ErrMsgM a
addErrMsg str = Maybe.maybe (Left str) Right

liftErrMsgM :: Monad m => ErrMsgM a -> ExceptT String m a
liftErrMsgM = ExceptT . return

safehd :: [a] -> Maybe a
safehd = takeFirstOf Just

recNat :: (Num nat, Enum nat) => (res) -> (nat -> res -> res) -> (nat -> res)
recNat my_init my_step n = foldr my_step my_init [n - 1, n - 2 .. 0]

(<^>) :: (fst1 -> fst2) -> (snd1 -> snd2) -> ((fst1, snd1) -> (fst2, snd2))
map_fst <^> map_snd = pure (curry id) <*> map_fst . fst <*> map_snd . snd

kconcat :: (Foldable.Foldable t, Monad m) => t (a -> m a) -> (a -> m a)
kconcat = Foldable.foldr (>=>) return

mkCantorPair :: (Num nat, Enum nat) => nat -> (nat, nat)
mkCantorPair = recNat (0, 0) (\n -> uncurry $ \x -> \y -> if null [0, 1 .. pred x] then (succ y, 0) else (pred x, succ y))

areAllDistinct :: Eq a => [a] -> Bool
areAllDistinct [] = True
areAllDistinct (x : xs) = notElem x xs && areAllDistinct xs

getGCD :: Integral int => int -> int -> PositiveInteger
getGCD x y
    | negate 1 `elem` map signum [x, y] = Function.on getGCD abs x y
    | 0 `elem` [x, y] = if x == y then error "Z.Algorithms.getGCD: only zero inputs" else Function.on (+) toInteger x y
    | otherwise = Function.on euclid toInteger x y
    where
        euclid :: MyNat -> MyNat -> PositiveInteger
        euclid a b = case a `mod` b of
            0 -> b
            c -> euclid b c

digraph :: forall vertex output. (Ord vertex, Monoid output, HasCallStack) => Set.Set vertex -> (vertex -> vertex -> Bool) -> (vertex -> output) -> Map.Map vertex output
digraph your_X your_R your_F' = Map.map snd (snd (snd (Identity.runIdentity (runStateT (mapM_ (go 1) your_X) ([], Map.fromSet (const (0, mempty)) your_X))))) where
    go :: Int -> vertex -> StateT ([vertex], Map.Map vertex (Int, output)) Identity.Identity ()
    go k x = do
        (stack, _N_F) <- get
        when (fst (_N_F Map.! x) == 0) $ do
            put (x : stack, Map.adjust (const (k, your_F' x)) x _N_F)
            forM_ your_X $ \y -> do
                when (your_R x y) $ do
                    (go $! succ k) y
                    (stack, _N_F) <- get
                    let (yN, yF) = _N_F Map.! y
                    put (stack, Map.adjust (min yN <^> mappend yF) x _N_F)
            (_, _N_F) <- get
            let (xN, xF) = _N_F Map.! x
            when (xN == k) $ do
                Function.fix $ \loop -> do
                    (stack, _N_F) <- get
                    let top = head stack
                    put (tail stack, Map.adjust (const (maxBound, xF)) top _N_F)
                    unless (top == x) $ do
                        loop

swords :: String -> [String]
swords s = filter (not . null) (takeWhile cond s : go (dropWhile cond s)) where
    cond :: Char -> Bool
    cond ch = ch `notElem` [' ', '\n', '\t', '\"', '\'']
    go :: String -> [String]
    go [] = []
    go (' ' : s) = go s
    go ('\n' : s) = go s
    go ('\t' : s) = go s
    go ('\"' : s) = case readStr s of
        Nothing -> app "\"" (go s)
        Just (s, str) -> str : go s
    go ('\'' : s) = case readChr s of
        Nothing -> app "\'" (go s)
        Just (s, chr) -> chr : go s
    go s = swords s
    app :: String -> [String] -> [String]
    app s [] = [s]
    app s (s1 : ss2) = (s ++ s1) : ss2
    readStr :: String -> Maybe (String, String)
    readStr [] = Nothing
    readStr ('\"' : s) = return (s, "")
    readStr ('\\' : 'n' : s) = fmap (fmap (kons '\n')) (readStr s)
    readStr ('\\' : 't' : s) = fmap (fmap (kons '\t')) (readStr s)
    readStr ('\\' : '\\' : s) = fmap (fmap (kons '\\')) (readStr s)
    readStr ('\\' : '\'' : s) = fmap (fmap (kons '\'')) (readStr s)
    readStr ('\\' : '\"' : s) = fmap (fmap (kons '\"')) (readStr s)
    readStr ('\\' : _) = error "Z.Algoritms.swords.readStr: bad input"
    readStr ('\n' : _) = error "Z.Algoritms.swords.readStr: bad input"
    readStr ('\t' : _) = error "Z.Algoritms.swords.readStr: bad input"
    readStr (c : s) = fmap (fmap (kons c)) (readStr s)
    readChr :: String -> Maybe (String, String)
    readChr [] = Nothing
    readChr ('\'' : s) = return (s, "")
    readChr ('\\' : 'n' : s) = fmap (fmap (kons '\n')) (readChr s)
    readChr ('\\' : 't' : s) = fmap (fmap (kons '\t')) (readChr s)
    readChr ('\\' : '\\' : s) = fmap (fmap (kons '\\')) (readChr s)
    readChr ('\\' : '\'' : s) = fmap (fmap (kons '\'')) (readChr s)
    readChr ('\\' : '\"' : s) = fmap (fmap (kons '\"')) (readChr s)
    readChr ('\\' : _) = error "Z.Algoritms.swords.readCtr: bad input"
    readChr ('\n' : _) = error "Z.Algoritms.swords.readCtr: bad input"
    readChr ('\t' : _) = error "Z.Algoritms.swords.readCtr: bad input"
    readChr (c : s) = fmap (fmap (kons c)) (readChr s)

tSortedSCCs :: Ord vertex => DigraphOf vertex -> [StrongConnectedComponent vertex]
tSortedSCCs = Identity.runIdentity . go where
    when' :: (Functor m, Monoid a) => Bool -> m a -> m a
    when' cond = if cond then id else fmap (const mempty)
    sortByRel :: Ord node => [node] -> StateT (Set.Set node) (ReaderT (node -> [node]) Identity.Identity) [node]
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
    splitByRel :: Ord node => [node] -> StateT (Set.Set node) (ReaderT (node -> [node]) Identity.Identity) [StrongConnectedComponent node]
    splitByRel [] = return []
    splitByRel (cur : nexts) = do
        visteds <- get
        cur_out <- when' (not (cur `Set.member` visteds)) $ do
            scc <- sortByRel [cur]
            return [SCC { hasLoop = cur `elem` scc, myNodes = Set.fromAscList scc }]
        nexts_out <- splitByRel nexts
        return (cur_out ++ nexts_out)
    go :: Ord node => Map.Map node (Set.Set node) -> Identity.Identity [StrongConnectedComponent node]
    go given_digraph = do
        let nodes = Set.toAscList (foldr Set.union (Map.keysSet given_digraph) (Map.elems given_digraph))
            froms = maybe [] Set.toAscList . flip Map.lookup given_digraph
            intos = Set.toAscList . Map.keysSet . flip Map.filter given_digraph . Set.member
        (sorted_nodes, _) <- runReaderT (runStateT (sortByRel nodes) Set.empty) froms
        (sorted_sccs, _) <- runReaderT (runStateT (splitByRel sorted_nodes) Set.empty) intos
        return sorted_sccs

mSort :: IncreasingOrdering element -> [element] -> [element]
mSort = go where
    merge :: IncreasingOrdering a -> [a] -> [a] -> [a]
    merge leq (y : ys) (z : zs) = if y `leq` z then y : merge leq ys (z : zs) else z : merge leq (y : ys) zs
    merge leq ys zs = ys ++ zs
    go :: IncreasingOrdering a -> [a] -> [a]
    go leq xs
        = case length xs `div` 2 of
            0 -> xs
            n -> uncurry (merge leq) . (go leq <^> go leq) $ splitAt n xs

instance Failable Bool where
    alt (False) = id
    alt x = const x

instance Failable (Maybe a) where
    alt (Nothing) = id
    alt x = const x

instance Failable (Either e a) where
    alt (Left _) = id
    alt x = const x

instance Failable [a] where
    alt [] = id
    alt x = const x

instance Failable b => Failable (a -> b) where
    alt = liftM2 alt

instance FailableZero Bool where
    nil = False

instance FailableZero (Maybe a) where
    nil = Nothing

instance FailableZero [a] where
    nil = []

instance FailableZero b => FailableZero (a -> b) where
    nil = const nil
