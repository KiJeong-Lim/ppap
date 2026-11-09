module Main where

import Control.Monad
import Control.Monad.Trans.Reader
import Data.IORef
import qualified Data.IntMap.Strict as IntMap
import qualified Data.Map.Strict as Map
import Hol.BETA.Constant
import Hol.BETA.Header
import Hol.BETA.HOPU
import Hol.BETA.TermNode
import Z.Utils

v :: Int -> TermNode
v i = mkLVar (LV_Unique (Unique i) noHint)

n :: Int -> TermNode
n i = mkNCon (DC_Unique (Unique i) noHint)

c :: Int -> TermNode
c i = mkNCon (DC_Named ("c" ++ show i))

a :: TermNode -> TermNode -> TermNode
a = mkNApp

l :: TermNode -> TermNode
l = mkNLamHint Nothing

i :: Int -> TermNode
i = mkNIdx

cases :: [(String, [(TermNode, TermNode)])]
cases = fixedCases ++ generatedCases

fixedCases :: [(String, [(TermNode, TermNode)])]
fixedCases =
    [ ("scope failure", [(v 0, n 10)])
    , ("occurs", [(v 0, a (c 1) (v 0))])
    , ("capture", [(v 0, a (l (l (i 1))) (c 1))])
    , ("eta", [(v 0, l (a (c 1) (i 0)))])
    , ("eta under binder", [(l (l (a (i 1) (i 0))), l (i 0))])
    , ("scope abstraction", [(a (v 0) (n 10), n 10)])
    , ("flex-flex", [(a (v 0) (n 10), a (v 1) (n 11))])
    , ("lbeta", [(a (v 0) (n 10), a (a (c 1) (a (a (v 1) (n 10)) (n 11))) (a (a (v 2) (n 10)) (n 10)))])
    , ("duplicate pruning", [(a (v 0) (n 10), a (a (v 1) (n 10)) (n 10))])
    , ("same head", [(a (a (v 0) (n 10)) (n 11), a (a (v 0) (n 10)) (n 12))])
    , ("pending", [(a (v 0) (c 1), c 2)])
    , ("pending solves", [(a (v 0) (c 1), c 2), (v 0, l (c 2))])
    , ("pending fails", [(a (v 0) (c 1), c 2), (v 0, l (c 3))])
    , ("pending inside binder", [(l (a (v 0) (a (c 1) (i 0))), l (i 0))])
    , ("partial bind rollback", [(a (v 0) (n 10), a (a (c 1) (v 1)) (a (v 2) (c 2)))])
    , ("scope raising", [(a (v 0) (n 10), v 3)])
    , ("scope pruning", [(v 0, a (v 3) (n 11))])
    , ("nested abstraction", [(a (v 0) (n 10), l (a (a (c 1) (n 10)) (i 0)))])
    , ("same head eta", [(a (v 0) (n 10), l (a (a (v 0) (n 10)) (i 0)))])
    , ("successor", [(a (mkNCon DC_Succ) (v 0), mkNCon (DC_NatL 9))])
    , ("zero successor failure", [(a (mkNCon DC_Succ) (v 0), mkNCon (DC_NatL 0))])
    , ("wildcard", [(a (v 0) (n 10), mkNCon DC_wc)])
    ]

-- Each pool has one simple type: i, i -> i, or i -> i -> i.
-- F/G/H are consistently unary/binary/unary; this excludes untyped omega terms.
generatedCases :: [(String, [(TermNode, TermNode)])]
generatedCases = concat
    [ [("seeded " ++ show group ++ "/" ++ show index, [(pick seed pool, pick next pool)]) | (index, (seed, next)) <- zip [0 :: Int .. 63] (zip seeds (drop 1 seeds))]
    | (group, pool) <- zip [0 :: Int ..] pools
    ]
    where
        seeds = tail (iterate (\seed -> (1664525 * seed + 1013904223) `mod` 4294967296) (2047 :: Integer))
        pick seed pool = pool !! fromInteger (seed `mod` toInteger (length pool))
        atoms = [c 2, c 3, n 10, n 11, n 12, v 2]
        ground = atoms ++ [a head arg | head <- [v 0, v 3, c 1], arg <- atoms]
            ++ [a (a (v 1) x) y | (x, y) <- zip atoms (reverse atoms)]
        unary = [v 0, v 3, c 1] ++ map (a (v 1)) atoms
            ++ map l (atoms ++ [i 0, a (v 0) (i 0), a (c 1) (i 0), a (a (v 1) (i 0)) (n 10), a (a (v 1) (n 10)) (i 0)])
        binary = v 1 : map (l . l)
            [i 0, i 1, v 2, n 10, a (v 0) (i 0), a (v 3) (i 1), a (a (v 1) (i 1)) (i 0), a (a (v 1) (i 0)) (i 1)]
        pools = [ground, unary, binary]

initial :: Labeling
initial = Labeling (IntMap.fromList [(10, 1), (11, 2), (12, 3)]) (IntMap.fromList [(0, 0), (1, 0), (2, 0), (3, 1)]) IntMap.empty IntMap.empty Map.empty IntMap.empty Map.empty

wire :: Labeling -> TermNode -> [Integer]
wire labeling term = case rewrite NF term of
    LVar variable -> [0, toInteger (lvKey variable), toInteger (lookupLabel variable labeling), if isTyLVar variable then 1 else 0, -1]
    NCon (DC (DC_Unique (Unique uid) _)) _ -> [5, toInteger uid, toInteger (lookupLabel (DC (DC_Unique (Unique uid) noHint)) labeling), -1]
    NCon (DC (DC_Named ('c' : number))) _ -> [1, read number, -1]
    NCon (DC DC_Succ) _ -> [1, 0, -1]
    NCon (DC DC_wc) _ -> [7]
    NCon (DC (DC_NatL value)) _ -> [6, toInteger (length (show value))] ++ map (toInteger . fromEnum) (show value)
    NIdx index -> [3, toInteger index]
    NLam _ _ body _ -> [4, -1] ++ wire labeling body
    NApp function argument _ -> [2, -1] ++ wire labeling function ++ wire labeling argument
    _ -> error "unsupported differential term"

sized :: [Integer] -> [Integer]
sized words = toInteger (length words) : words

main :: IO ()
main = forM_ cases $ \(name, equations) -> do
    counter <- newIORef 100
    result <- runReaderT (runUniqueT (go initial mempty [] equations)) counter
    let input = [4] ++ concatMap (sized . wire initial . v) [0, 1, 2, 3] ++ [3] ++ concatMap (sized . wire initial . n) [10, 11, 12] ++ [toInteger (length equations)] ++ concat [sized (wire initial lhs) ++ sized (wire initial rhs) | (lhs, rhs) <- equations]
        output = case result of
            Nothing -> [0]
            Just (labeling, subst, pending) -> [1, 4] ++ concatMap (sized . wire labeling . bindVars subst . v) [0, 1, 2, 3] ++ [toInteger (length pending)] ++ concat [sized (wire labeling lhs) ++ sized (wire labeling rhs) | lhs :=?=: rhs <- pending]
    putStrLn (show name)
    putStrLn (show input)
    putStrLn (show output)
    where
        go labeling subst pending [] = return (Just (labeling, subst, pending))
        go labeling subst pending ((lhs, rhs) : rest) = do
            result <- runHOPU labeling ((bindVars subst lhs :=?=: bindVars subst rhs) : pending)
            case result of
                Nothing -> return Nothing
                Just (pending', HopuSol labeling' theta) -> go labeling' (theta <> subst) pending' rest
