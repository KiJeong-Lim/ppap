-- Thanks to EatChangmyeong (https://eatchangmyeong.github.io/)
module PGS.LALR where

import GHC.Stack (HasCallStack)
import Data.Maybe (mapMaybe, isNothing, listToMaybe)
import Data.Tuple (swap)
import Data.List (intercalate, uncons)
import Data.Set (Set)
import qualified Data.Set as Set hiding (Set)
import qualified Data.IntSet as IntSet hiding (IntSet)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map hiding (Map)
import qualified Data.Map.Merge.Strict as MapMerge
import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IntMap hiding (IntMap)
import Control.Monad (guard)
import Z.Utils (List)

type LRItemSet terminal nonterminal = Map (LRItem terminal nonterminal) (Set [terminal]) -- LR(n) item set with mapping to lookahead sets

type LRAutomaton terminal nonterminal = IntMap (LRState terminal nonterminal) -- LR(n) automaton

data Symbol terminal nonterminal
    = TSym (terminal)
    | NSym (nonterminal)
    deriving (Eq, Ord, Show)

data Rule terminal nonterminal
    = Rule
        { lhs :: !(nonterminal) -- LHS of the rule
        , rhs :: !(List (Symbol terminal nonterminal)) -- RHS of the rule, ordered list of 0 or more symbols
        }
    deriving (Eq, Ord, Show)

data CFG terminal nonterminal
    = CFG
        { start :: !(nonterminal) -- starting symbol
        , rules :: !(IntMap (Rule terminal nonterminal)) -- set of rules
        }
    deriving (Eq, Ord, Show)

data LRItem terminal nonterminal -- single LR(0) item
    = LRItem
        { rule :: !(Int) -- zero-based rule number from CFG
        , handle :: !(Int) -- zero-based position of handle
        }
    deriving (Eq, Ord, Show)

data LRState terminal nonterminal
    = LRState
        { kernel :: !(LRItemSet terminal nonterminal)
        -- "kernel" is the item subset that "initiates" the full item set, whose elements are either:
        -- * "genesis" items in the starting state, whose lhs is starting symbol and has zero handle position
        -- * "shifted" items with nonzero handle position
        , transition :: !(Map (Symbol terminal nonterminal) Int)
        -- Index of the next state when shifted by a symbol
        }
    deriving (Eq, Ord, Show)

data Action -- Possible entries in the ACTION table
    = Shift -- shift targets are described in the GOTO table
    | Reduce (Int)
    | Accept
    | Conflict (List Action)
    deriving (Eq, Ord, Show)

data LRTable terminal nonterminal -- LR(n) parsing table
    = LRTable
        { lookahead :: !(Int) -- lookahead length
        , reduceLUT :: !(IntMap (nonterminal, Int)) -- ruleset information for reduction
        , action :: !(Map (Int, [terminal]) Action) -- ACTION table
        , goto :: !(Map (Int, Symbol terminal nonterminal) Int) -- GOTO table
        }
    deriving (Eq, Show)

data ParseTree terminal nonterminal -- parse tree
    = Terminal (terminal)
    | Nonterminal (nonterminal) (List (ParseTree terminal nonterminal))
    deriving (Show)

fixpointWithInit :: Eq a => (a -> a) -> a -> a
-- fixpoint combinator based on `==`
fixpointWithInit f x = let x' = f x in if x == x' then x' else fixpointWithInit f x'

unionItemSet :: Ord terminal => LRItemSet terminal nonterminal -> LRItemSet terminal nonterminal -> LRItemSet terminal nonterminal
-- `Set.union` but for item sets
unionItemSet = Map.unionWith Set.union

unionsItemSet :: (Ord terminal, Foldable foldable) => foldable (LRItemSet terminal nonterminal) -> LRItemSet terminal nonterminal
-- `Set.unions` but for item sets
unionsItemSet = Map.unionsWith Set.union

excludeItemSet :: Ord terminal => LRItemSet terminal nonterminal -> LRItemSet terminal nonterminal -> LRItemSet terminal nonterminal
-- `Set.\\` but for item sets
excludeItemSet = MapMerge.merge MapMerge.preserveMissing' MapMerge.dropMissing $ MapMerge.zipWithMaybeMatched go where
    go _ xs ys = let zs = xs Set.\\ ys in zs <$ guard (not $ Set.null zs)

mapMaybeKeys :: Ord b => (a -> Maybe b) -> Map a c -> Map b c
-- `Map.mapMaybe` but with keys
mapMaybeKeys f m = Map.fromList [ (k', v) | (k, v) <- Map.toList m, Just k' <- pure (f k) ] 

ruleToItem :: Int -> LRItem terminal nonterminal
-- construct an LR(0) item from rule index
ruleToItem r = LRItem { rule = r, handle = 0 }

itemSetToState :: LRItemSet terminal nonterminal -> LRState terminal nonterminal
-- construct a LR(m) state from the kernel, without any transition
itemSetToState item_set = LRState { kernel = item_set, transition = Map.empty }

first :: (HasCallStack, Ord nonterminal) => Map nonterminal (Set [terminal]) -> Symbol terminal nonterminal -> Set [terminal]
-- FIRST set of single symbol
first first_set (TSym ts) = Set.singleton [ts]
first first_set (NSym ns) = first_set Map.! ns

firsts :: (Ord terminal, Ord nonterminal) => Int -> Map nonterminal (Set [terminal]) -> [Symbol terminal nonterminal] -> Set [terminal]
-- `first` but "lifted" for string of symbols
-- this set is calculated by `concatTake`ing the FIRST set of each symbol
-- m stands for LR(m)
firsts m first_set = firsts' m first_set (Set.singleton [])

firsts' :: (Ord terminal, Ord nonterminal) => Int -> Map nonterminal (Set [terminal]) -> Set [terminal] -> [Symbol terminal nonterminal] -> Set [terminal]
-- `firsts` but with a final lookahead set as padding
firsts' m first_set look_ahead = Set.map (take m) . foldr (liftM2append . first first_set) look_ahead where
    liftM2append :: Ord a => Set [a] -> Set [a] -> Set [a]
    liftM2append xss yss = Set.fromList [ xs ++ ys | xs <- Set.toList xss, ys <- Set.toList yss ]

rulesAbout :: Eq nonterminal => nonterminal -> IntMap (Rule terminal nonterminal) -> IntMap (Rule terminal nonterminal)
-- all rules that has `n` as lhs
rulesAbout n = IntMap.filter (\rule -> lhs rule == n)

ruleIndicesAbout :: Eq nonterminal => nonterminal -> IntMap (Rule terminal nonterminal) -> [Int]
-- indices of all rules that has `n` as lhs
ruleIndicesAbout n = IntMap.keys . rulesAbout n

nextSymbol :: HasCallStack => CFG terminal nonterminal -> LRItem terminal nonterminal -> Maybe (Symbol terminal nonterminal)
-- the next expected symbol, that is, the first one after the handle
-- returns `Nothing` if the handle is at the end
nextSymbol cfg item = expansion !! pos <$ guard (pos < length expansion) where
    pos = handle item
    expansion = rhs $ rules cfg IntMap.! rule item

afterHandle :: HasCallStack => CFG terminal nonterminal -> LRItem terminal nonterminal -> [Symbol terminal nonterminal]
-- substring after the item's handle
afterHandle cfg item = drop (handle item) $ rhs $ rules cfg IntMap.! rule item

shift :: (Ord terminal, Ord nonterminal) => CFG terminal nonterminal -> Symbol terminal nonterminal -> LRItemSet terminal nonterminal -> LRItemSet terminal nonterminal
-- "shift" a symbol into an item set
-- if a member item expects the given symbol, the handle advances by one
-- otherwise, it is discarded from the set
shift cfg symbol = mapMaybeKeys (\it -> it { handle = handle it + 1 } <$ guard (Just symbol == nextSymbol cfg it))

shiftableSymbols :: (Ord terminal, Ord nonterminal) => CFG terminal nonterminal -> LRItemSet terminal nonterminal -> Set (Symbol terminal nonterminal)
-- find every shiftable symbol in the given item set
shiftableSymbols cfg = Set.fromList . mapMaybe (nextSymbol cfg) . Map.keys

shiftableLookaheads :: (Ord terminal, Ord nonterminal) => Int -> CFG terminal nonterminal -> Map nonterminal (Set [terminal]) -> LRItemSet terminal nonterminal -> Set [terminal]
-- find every lookahead string eligible for SHIFT action
shiftableLookaheads m cfg first_set items = Set.fromList [ la | (item, las) <- Map.toList items, isJustTSym (nextSymbol cfg item), let str = afterHandle cfg item, la <- Set.toList (firsts' m first_set las str), not (null la) ] where
    isJustTSym (Just (TSym _)) = True
    isJustTSym _ = False

reducibleRules :: CFG terminal nonterminal -> LRItemSet terminal nonterminal -> IntMap (Set [terminal])
-- find every rule and associated lookahead sets eligible for REDUCE action
reducibleRules cfg items = IntMap.fromList [ (rule item, la) | (item, la) <- Map.toList items, isNothing (nextSymbol cfg item) ]

close :: (HasCallStack, Ord terminal, Ord nonterminal) => Int -> CFG terminal nonterminal -> Map nonterminal (Set [terminal]) -> LRItemSet terminal nonterminal -> LRItemSet terminal nonterminal
-- close the LR(m) item set
-- returned set includes original items
close m cfg first_set = fixpointWithInit $ \its -> unionsItemSet (its : map once (Map.toList its)) where
    once (item, la) = case nextSymbol cfg item of
        Just (NSym nterm) -> Map.fromList [ (ruleToItem i, firsts' m first_set la (drop (handle item + 1) (rhs (rules cfg IntMap.! rule item)))) | i <- ruleIndicesAbout nterm (rules cfg) ]
        _ -> Map.empty

fullItemSet :: (Ord terminal, Ord nonterminal) => Int -> CFG terminal nonterminal -> Map nonterminal (Set [terminal]) -> LRState terminal nonterminal -> LRItemSet terminal nonterminal
-- full item set of a state, including closures
fullItemSet m cfg first_set = close m cfg first_set . kernel

firstSetFrom :: (Ord terminal, Ord nonterminal) => Int -> IntMap (Rule terminal nonterminal) -> Map nonterminal (Set [terminal])
-- find FIRST set table for each nonterminals from given derivation rules
firstSetFrom m rule_set = fixpointWithInit (\first_set -> IntMap.foldl' propagate first_set rule_set) $ Map.fromList [ (lhs item, Set.empty) | item <- IntMap.elems rule_set ] where
    propagate first_set rule = Map.adjust (Set.union $ firsts m first_set $ rhs rule) (lhs rule) first_set

augment :: (Ord terminal, Ord nonterminal) => CFG terminal nonterminal -> CFG terminal (Maybe nonterminal)
-- augment the given CFG
-- new starting symbol is `Nothing`, existing nonterminals are applied `Just`
-- `Nothing ::= <old starting symbol>` is prepended as zeroth rule
augment cfg = CFG { start = Nothing, rules = IntMap.fromList ((0, Rule { lhs = Nothing, rhs = [NSym (Just (start cfg))]}) : zip [1, 2 .. ] [ Rule { lhs = Just (lhs rule), rhs = map newNSym (rhs rule) } | rule <- IntMap.elems (rules cfg) ]) } where
    newNSym (TSym ts) = TSym ts
    newNSym (NSym ns) = NSym (Just ns)

automatonFrom :: (HasCallStack, Ord terminal, Ord nonterminal) => Int -> CFG terminal nonterminal -> Map nonterminal (Set [terminal]) -> LRAutomaton terminal nonterminal
-- construct an LR(m) automaton from given CFG
-- entrypoint is the zeroth state
automatonFrom m cfg first_set = go (IntMap.singleton 0 $ itemSetToState set0) (Map.singleton set0 0) IntSet.empty [0] where
    set0 = Map.fromList [ (ruleToItem i, Set.singleton []) | i <- ruleIndicesAbout (start cfg) (rules cfg) ]
    go table lut visited [] = table
    go table lut visited (u : us)
        | u `IntSet.member` visited = go table lut visited us
        | otherwise = go table' lut' visited' (us ++ map fst unseen)
        where
            items = fullItemSet m cfg first_set $ table IntMap.! u
            shifted = Map.fromList [ (symbol, shift cfg symbol items) | symbol <- Set.toList (shiftableSymbols cfg items) ]
            unseen = zip [IntMap.size table .. ] [ item | item <- Map.elems shifted, item `Map.notMember` lut ]
            lut' = Map.union lut $ Map.fromList $ map swap unseen
            table' = IntMap.adjust (\s -> s { transition = Map.map (\item -> lut' Map.! item) shifted }) u $ IntMap.union table $ IntMap.fromList $ map (fmap itemSetToState) unseen
            visited' = IntSet.insert u visited

replaceLASet :: (HasCallStack, Ord terminal, Ord nonterminal) => Int -> CFG terminal nonterminal -> Map nonterminal (Set [terminal]) -> LRAutomaton terminal nonterminal -> LRAutomaton terminal nonterminal
-- reconstruct lookahead sets with given length `m`
-- if the new length is equal to the previous one, nothing practically changes
-- this function can generate LALR automata if the new length is longer
replaceLASet m cfg first_set automaton = fixpointWithInit go automaton where
    ts = IntMap.map transition automaton
    shiftOne (i, k) = [ (ts IntMap.! i Map.! symbol, shift cfg symbol items) | symbol <- Set.toList (shiftableSymbols cfg items) ] where
        items = close m cfg first_set k
    go table = foldr ($) table [ IntMap.adjust (\t -> t { kernel = unionItemSet k' (kernel t) }) i' | (i, k) <- IntMap.toList table, (i', k') <- shiftOne (i, fullItemSet m cfg first_set k) ]

tabulate :: (Ord terminal, Ord nonterminal) => Int -> CFG terminal (Maybe nonterminal) -> Map (Maybe nonterminal) (Set [terminal]) -> LRAutomaton terminal (Maybe nonterminal) -> LRTable terminal nonterminal
-- generate an LR(m) parsing table from given automaton
tabulate m cfg fs automaton = LRTable { lookahead = m, reduceLUT = lut, action = Map.mapMaybe (resolve . Set.toList) at, goto = gt } where
    lut = IntMap.fromList [ (i - 1, (lhs', length $ rhs r)) | (i, r) <- IntMap.toList (rules cfg), Just lhs' <- pure (lhs r) ]
    item_sets = IntMap.map (fullItemSet m cfg fs) automaton
    shifts = Set.fromList [ (i, la) | (i, item_set) <- IntMap.toList item_sets, la <- Set.toList (shiftableLookaheads m cfg fs item_set) ]
    reduces = Map.unionsWith Set.union $ map reducible $ IntMap.toList item_sets where
        reducible (s, item_set) = Map.fromList [ ((s, la), Set.singleton i) | (i, las) <- IntMap.toList (reducibleRules cfg item_set), la <- Set.toList las ]
    at = Map.unionWith Set.union (Map.fromList [ (s, Set.singleton Shift) | s <- Set.toList shifts ]) (Map.map (Set.map (\i -> if i == 0 then Accept else Reduce (i - 1))) reduces)
    gt = Map.fromList [ ((i, symbol), u) | (i, s) <- IntMap.toList automaton, (symbol', u) <- Map.toList (transition s), Just symbol <- pure (_Just symbol') ] where
        _Just (TSym ts) = pure (TSym ts)
        _Just (NSym ns') = fmap NSym ns'
    resolve [] = Nothing
    resolve [act] = Just act
    resolve acts = Just (Conflict acts)

lrTableFrom :: (Ord terminal, Ord nonterminal) => Int -> nonterminal -> [Rule terminal nonterminal] -> LRTable terminal nonterminal
-- generate an LR(m) parsing table from starting symbol and ruleset
lrTableFrom m s rule_set = tabulate m cfg first_set $ automatonFrom m cfg first_set where
    rule_set' = IntMap.fromList $ zip [0 .. ] rule_set
    cfg = augment $ CFG s rule_set'
    first_set = firstSetFrom m $ rules cfg

lalrTableFrom :: (Ord terminal, Ord nonterminal) => Int -> Int -> nonterminal -> [Rule terminal nonterminal] -> LRTable terminal nonterminal
-- generate an LA(k)LR(j) parsing table from starting symbol and ruleset
-- LA(k)LR(j) parsers are generated from LR(j) item sets but with k more lookahead tokens
-- LALR(m) corresponds to LA(m)LR(0)
-- cf. https://en.wikipedia.org/wiki/LALR_parser#Overview
lalrTableFrom k j s rule_set = tabulate (k + j) cfg first_set $ replaceLASet (k + j) cfg first_set $ automatonFrom j cfg first_set where
    rule_set' = IntMap.fromList $ zip [0 .. ] rule_set
    cfg = augment $ CFG s rule_set'
    first_set = firstSetFrom (k + j) $ rules cfg

parse :: (Ord terminal, Ord nonterminal) => LRTable terminal nonterminal -> [terminal] -> Maybe (ParseTree terminal nonterminal)
-- construct parsing tree from given list of terminal symbols
parse table = loop [] where
    loop stack ts = do
        let top = listToMaybe stack
            state = maybe 0 snd top
        act <- action table Map.!? (state, take (lookahead table) ts)
        case act of
            Accept -> fst <$> top
            Shift -> do
                (t, ts') <- uncons ts
                next <- goto table Map.!? (state, TSym t)
                loop ((Terminal t, next) : stack) ts'
            Reduce i -> do
                (n, l) <- reduceLUT table IntMap.!? i
                let (redex, stack') = splitAt l stack
                    tree = Nonterminal n $ reverse $ map fst redex
                    top' = listToMaybe stack'
                    state' = maybe 0 snd top'
                next <- goto table Map.!? (state', NSym n)
                loop ((tree, next) : stack') ts
            Conflict _ -> fail "action-conflict"

{- [TEST]

data TestTermLambda
    = Abs
    | OpenL
    | CloseL
    | VarE
    | VarU
    | Const
    deriving (Eq, Ord, Show)

data TestNontermLambda
    = T0
    | T1
    | T2
    | T3
    deriving (Eq, Ord, Show)
 
testRulesLambda :: [Rule TestTermLambda TestNontermLambda]
testRulesLambda =
    [ Rule T0 [TSym VarE, TSym Abs, NSym T0]
    , Rule T0 [TSym VarU, TSym Abs, NSym T0]
    , Rule T0 [NSym T1]
    , Rule T1 [NSym T2]
    , Rule T1 [NSym T2, TSym VarE, TSym Abs, NSym T0]
    , Rule T1 [NSym T2, TSym VarU, TSym Abs, NSym T0]
    , Rule T2 [NSym T3]
    , Rule T2 [NSym T2, NSym T3]
    , Rule T3 [TSym OpenL, NSym T0, TSym CloseL]
    , Rule T3 [TSym VarE]
    , Rule T3 [TSym VarU]
    , Rule T3 [TSym Const]
    ]

main :: IO ()
main = do
    let table = lalrTableFrom 1 0 T0 testRulesLambda
        testString = [VarU, VarE, Abs, VarU, VarE, OpenL, VarU, VarE, CloseL]
    print $ parse table testString

-}
