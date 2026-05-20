module Calc.Tools.Fuzzy where

import Control.Applicative (liftA2)
import Control.Monad (ap, replicateM)
import Data.List (minimumBy)
import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import Data.Ord (comparing)
import System.Random (randomRIO)

--------------------------------------------------------------------------------
-- Costs and fuzzy booleans
--------------------------------------------------------------------------------

type Cost = Double

zeroCost :: Cost
zeroCost = 0

infCost :: Cost
infCost = 1 / 0

sanitizeCost :: Cost -> Cost
sanitizeCost x
    | isNaN x   = infCost
    | x <= 0    = 0
    | otherwise = x

plusCost :: Cost -> Cost -> Cost
plusCost x y = sanitizeCost (sanitizeCost x + sanitizeCost y)

minCost :: Cost -> Cost -> Cost
minCost x y = min (sanitizeCost x) (sanitizeCost y)

showsCost :: Cost -> ShowS
showsCost x s
    | isNaN x        = "NaN" ++ s
    | isInfinite x   = "∞" ++ s
    | otherwise      = shows x s

newtype DBool
    = DBool { getCost :: Cost }
    deriving (Eq, Ord)

instance Show DBool where
    showsPrec _ (DBool x) = showsCost x

mkDBool :: Cost -> DBool
mkDBool = DBool . sanitizeCost

trueD :: DBool
trueD = mkDBool 0

falseD :: DBool
falseD = mkDBool infCost

fromBoolD :: Bool -> DBool
fromBoolD True  = trueD
fromBoolD False = falseD

andD :: DBool -> DBool -> DBool
andD (DBool x) (DBool y) = mkDBool (plusCost x y)

orD :: DBool -> DBool -> DBool
orD (DBool x) (DBool y) = mkDBool (minCost x y)

(.&&.) :: DBool -> DBool -> DBool
(.&&.) = andD

(.||.) :: DBool -> DBool -> DBool
(.||.) = orD

infixr 3 .&&.
infixr 2 .||.

allD :: [DBool] -> DBool
allD = foldr (.&&.) trueD

anyD :: [DBool] -> DBool
anyD = foldr (.||.) falseD

scaleD :: Cost -> DBool -> DBool
scaleD s (DBool x)
    | isNaN s || s <= 0 = mkDBool x
    | otherwise         = mkDBool (x / s)

weightD :: Cost -> DBool -> DBool
weightD w (DBool x)
    | isNaN w || w <= 0 = mkDBool x
    | otherwise         = mkDBool (w * x)

satisfiedD :: Cost -> DBool -> Bool
satisfiedD eps (DBool x) = sanitizeCost x <= max 0 eps

--------------------------------------------------------------------------------
-- Distance-valued primitive predicates
--------------------------------------------------------------------------------

-- | Cost to make x >= y true.
geD :: Double -> Double -> DBool
geD x y = mkDBool (max 0 (y - x))

-- | Cost to make x <= y true.
leD :: Double -> Double -> DBool
leD x y = mkDBool (max 0 (x - y))

-- | Cost to make x == y true.
eqD :: Double -> Double -> DBool
eqD x y = mkDBool (abs (x - y))

-- | Cost to make x < y true, with a strictness margin epsilon.
--   eps = 0 means the topological/inﬁmum distance to strict inequality.
ltDWith :: Double -> Double -> Double -> DBool
ltDWith eps x y = mkDBool (max 0 (x - y + abs eps))

-- | Cost to make x > y true, with a strictness margin epsilon.
--   eps = 0 means the topological/inﬁmum distance to strict inequality.
gtDWith :: Double -> Double -> Double -> DBool
gtDWith eps x y = mkDBool (max 0 (y - x + abs eps))

ltD :: Double -> Double -> DBool
ltD = ltDWith 0

gtD :: Double -> Double -> DBool
gtD = gtDWith 0

(>=?) :: Double -> Double -> DBool
(>=?) = geD

(<=?) :: Double -> Double -> DBool
(<=?) = leD

(==?) :: Double -> Double -> DBool
(==?) = eqD

infix 4 >=?, <=?, ==?

--------------------------------------------------------------------------------
-- Values with alternatives
--------------------------------------------------------------------------------

data Val a
    = Val
    { actual       :: a
    , alternatives :: [(a, Cost)]
    } deriving (Show)

pureVal :: a -> Val a
pureVal x = Val x []

alternativesOf :: Val a -> [(a, Cost)]
alternativesOf (Val _ xs) =
    [ (a, c') 
    | (a, c) <- xs
    , let c' = sanitizeCost c
    , not (isInfinite c')
    ]

choices :: Val a -> [(a, Cost)]
choices v = (actual v, zeroCost) : alternativesOf v

support :: Ord a => Val a -> Map a Cost
support v = Map.fromListWith minCost (choices v)

costOf :: Ord a => a -> Val a -> Cost
costOf x v = Map.findWithDefault infCost x (support v)

normalize :: Ord a => Val a -> Val a
normalize v = Val (actual v) (Map.toList (Map.delete (actual v) (support v)))

eqVal :: Ord a => Val a -> Val a -> Bool
eqVal v w = actual v == actual w && support v == support w

instance Ord a => Eq (Val a) where
    (==) = eqVal

instance Functor Val where
    fmap f v = v >>= (pure . f)

instance Applicative Val where
    pure = pureVal
    (<*>) = ap

instance Monad Val where
    Val x xs >>= k = Val y (ys ++ concatMap expandAlternative (alternativesOf (Val x xs))) where
        actualPath = k x
        y          = actual actualPath
        ys         = alternativesOf actualPath
        expandAlternative (a, c) =
            [ (b, plusCost c d)
            | (b, d) <- choices (k a)
            ]

instance Num a => Num (Val a) where
    (+)         = liftA2 (+)
    (-)         = liftA2 (-)
    (*)         = liftA2 (*)
    negate      = fmap negate
    abs         = fmap abs
    signum      = fmap signum
    fromInteger = pure . fromInteger

instance Fractional a => Fractional (Val a) where
    (/)          = liftA2 (/)
    recip        = fmap recip
    fromRational = pure . fromRational

instance Floating a => Floating (Val a) where
    pi      = pure pi
    exp     = fmap exp
    log     = fmap log
    sin     = fmap sin
    cos     = fmap cos
    asin    = fmap asin
    acos    = fmap acos
    atan    = fmap atan
    sinh    = fmap sinh
    cosh    = fmap cosh
    asinh   = fmap asinh
    acosh   = fmap acosh
    atanh   = fmap atanh

-- | Build a valued Boolean from its current truth value and the costs
--   for making it True/False.
boolV :: Bool -> Cost -> Cost -> Val Bool
boolV b trueCost falseCost = if b then Val True  [(False, sanitizeCost falseCost)] else Val False [(True,  sanitizeCost trueCost)]

-- | Ordinary conditional, but over Val Bool.  This preserves the nearby
--   alternative branch and its branch-switching cost.
ifThenElse :: Val Bool -> Val a -> Val a -> Val a
ifThenElse c t e = do
    b <- c
    if b then t else e

truthCost :: Val Bool -> DBool
truthCost v = mkDBool (costOf True v)

falsityCost :: Val Bool -> DBool
falsityCost v = mkDBool (costOf False v)

geRawV :: Double -> Double -> Val Bool
geRawV x y = boolV (x >= y) (getCost (geD x y)) (getCost (ltD x y))

leRawV :: Double -> Double -> Val Bool
leRawV x y = boolV (x <= y) (getCost (leD x y)) (getCost (gtD x y))

ltRawV :: Double -> Double -> Val Bool
ltRawV x y = boolV (x < y) (getCost (ltD x y)) (getCost (geD x y))

gtRawV :: Double -> Double -> Val Bool
gtRawV x y = boolV (x > y) (getCost (gtD x y)) (getCost (leD x y))

eqRawV :: Double -> Double -> Val Bool
eqRawV x y = boolV (x == y) (getCost (eqD x y)) 0

geV :: Val Double -> Val Double -> Val Bool
geV x y = x >>= \x' -> y >>= \y' -> geRawV x' y'

leV :: Val Double -> Val Double -> Val Bool
leV x y = x >>= \x' -> y >>= \y' -> leRawV x' y'

ltV :: Val Double -> Val Double -> Val Bool
ltV x y = x >>= \x' -> y >>= \y' -> ltRawV x' y'

gtV :: Val Double -> Val Double -> Val Bool
gtV x y = x >>= \x' -> y >>= \y' -> gtRawV x' y'

eqV :: Val Double -> Val Double -> Val Bool
eqV x y = x >>= \x' -> y >>= \y' -> eqRawV x' y'

(.>=.) :: Val Double -> Val Double -> Val Bool
(.>=.) = geV

(.<=.) :: Val Double -> Val Double -> Val Bool
(.<=.) = leV

(.<.) :: Val Double -> Val Double -> Val Bool
(.<.) = ltV

(.>.) :: Val Double -> Val Double -> Val Bool
(.>.) = gtV

(.==.) :: Val Double -> Val Double -> Val Bool
(.==.) = eqV

infix 4 .>=., .<=., .<., .>., .==.

--------------------------------------------------------------------------------
-- A small derivative-free minimizer
--------------------------------------------------------------------------------

type Point = [Double]
type Box = [(Double, Double)]

data Config
    = Config
    { restarts    :: Int
    , iterations  :: Int
    , initialStep :: Double
    , minStep     :: Double
    , shrinkStep  :: Double
    , epsilon     :: Double
    } deriving (Eq, Show)

defaultConfig :: Config
defaultConfig
    = Config
    { restarts    = 40
    , iterations  = 800
    , initialStep = 0.25
    , minStep     = 1e-8
    , shrinkStep  = 0.5
    , epsilon     = 1e-9
    }

data Result
    = Result
    { bestPoint      :: Point
    , bestCost       :: Cost
    , usedIterations :: Int
    } deriving (Eq, Show)

normaliseBound :: (Double, Double) -> (Double, Double)
normaliseBound (lo, hi)
    | lo <= hi  = (lo, hi)
    | otherwise = (hi, lo)

normaliseBox :: Box -> Box
normaliseBox = map normaliseBound

clip :: (Double, Double) -> Double -> Double
clip b0 x = max lo (min hi x) where
    (lo, hi) = normaliseBound b0 

randomPoint :: Box -> IO Point
randomPoint box = mapM randomRIO (normaliseBox box)

replaceAt :: Int -> a -> [a] -> [a]
replaceAt i y xs = take i xs ++ [y] ++ drop (i + 1) xs

neighbours :: Box -> Double -> Point -> [Point]
neighbours box0 step xs = do
    (i, ((lo, hi), x)) <- zip [0..] (zip (normaliseBox box0) xs)
    dir <- [-1.0, 1.0]
    let width = hi - lo
        x' = clip (lo, hi) (x + dir * step * width)
    return (replaceAt i x' xs )

safeObjective :: (Point -> Cost) -> Point -> Cost
safeObjective f x = sanitizeCost (f x)

localSearchCost :: Config -> Box -> (Point -> Cost) -> Point -> Result
localSearchCost cfg box objective x0 = go 0 (initialStep cfg) x0 (safeObjective objective x0) where
    maxIters = max 0 (iterations cfg)
    eps      = max 0 (epsilon cfg)
    go :: Int -> Double -> Point -> Cost -> Result
    go n step x fx
        | n >= maxIters = Result x fx n
        | fx <= eps = Result x fx n
        | step <= minStep cfg = Result x fx n
        | otherwise = if fx' < fx then go (n + 1) step x' fx' else go (n + 1) (step * shrinkStep cfg) x fx where
            candidates = x : neighbours box step x
            scored     = [ (p, safeObjective objective p) | p <- candidates ]
            (x', fx')  = minimumBy (comparing snd) scored

minimizeCost :: Config -> Box -> (Point -> Cost) -> IO Result
minimizeCost cfg box objective = do
  starts <- replicateM (max 1 (restarts cfg)) (randomPoint box)
  let results = map (localSearchCost cfg box objective) starts
  pure (minimumBy (comparing bestCost) results)

minimize :: Config -> Box -> (Point -> DBool) -> IO Result
minimize cfg box objective = minimizeCost cfg box (getCost . objective)
