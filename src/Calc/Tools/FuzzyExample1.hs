
module Calc.Tools.FuzzyExample1 where

import Calc.Tools.Fuzzy
import Text.Printf (printf)

--------------------------------------------------------------------------------
-- Example 1: find a value in a narrow interval
--------------------------------------------------------------------------------

badNarrowInterval :: Point -> DBool
badNarrowInterval [x] = (x >=? 10.0) .&&. (x <=? 10.1)
badNarrowInterval _ = falseD

boolBadNarrowInterval :: Point -> Bool
boolBadNarrowInterval [x] = 10.0 <= x && x <= 10.1
boolBadNarrowInterval _ = False

--------------------------------------------------------------------------------
-- Example 2: toy braking-controller counterexample
--------------------------------------------------------------------------------

brakeAcceleration :: Double
brakeAcceleration = 8.0

reactionTime :: Double
reactionTime = 1.0

stoppingDistance :: Double -> Double
stoppingDistance v = reactionTime * v + v * v / (2 * brakeAcceleration)

-- Bad situation:
--   1. stopping distance >= current distance, so the car needs braking;
--   2. distance >= 25, so the toy controller does not brake.
badController :: Point -> DBool
badController [speed, distance] = (stoppingDistance speed >=? distance) .&&. (distance >=? 25.0)
badController _ = falseD

boolBadController :: Double -> Double -> Bool
boolBadController speed distance = stoppingDistance speed >= distance && distance >= 25.0

--------------------------------------------------------------------------------
-- Example 3: Val Bool preserves a nearby branch
--------------------------------------------------------------------------------

branchExample :: Val String
branchExample = ifThenElse (geRawV 9.9 10.0) (pure "then branch: x >= 10.0") (pure "else branch: x < 10.0")

printResult :: Result -> IO ()
printResult r = do
  putStrLn ("best point = " ++ show (bestPoint r))
  putStrLn ("best cost  = " ++ show (bestCost r))
  putStrLn ("iterations = " ++ show (usedIterations r))

main :: IO ()
main = do
    let cfg = defaultConfig { restarts = 80, iterations = 1200 }

    putStrLn "Example 1: searching for x such that 10.0 <= x <= 10.1"
    r1 <- minimize cfg [(0, 1000)] badNarrowInterval
    printResult r1
    putStrLn ("verified by Bool? " ++ show (boolBadNarrowInterval (bestPoint r1)))
    putStrLn ""

    putStrLn "Example 2: searching for a braking-controller counterexample"
    r2 <- minimize cfg [(0, 50), (0, 200)] badController
    printResult r2
    case bestPoint r2 of
        [speed, distance] -> do
            printf "speed     = %.6f\n" speed
            printf "distance  = %.6f\n" distance
            printf "stopping  = %.6f\n" (stoppingDistance speed)
            putStrLn ("verified by Bool? " ++ show (boolBadController speed distance))
        _ -> pure ()
    putStrLn ""

    putStrLn "Example 3: Val branch information"
    putStrLn ("raw       = " ++ show branchExample)
    putStrLn ("normalized= " ++ show (normalize branchExample))
