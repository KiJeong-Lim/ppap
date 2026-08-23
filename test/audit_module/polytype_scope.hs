module Main where

import Hol.BETA.Header
import Hol.BETA.ModuleLoader (polyTypeEq)
import System.Exit (exitFailure)

main :: IO ()
main
    | not (polyTypeEq alphaLeft alphaRight) = exitFailure
    | polyTypeEq malformedHigh malformedHigh = exitFailure
    | polyTypeEq malformedNegative malformedNegative = exitFailure
    | otherwise = putStrLn "polytype scope checks passed"
    where
        alphaLeft = Forall ["A", "B"] (TyVar 0 `mkTyArrow` TyVar 1)
        alphaRight = Forall ["Y", "X"] (TyVar 1 `mkTyArrow` TyVar 0)
        malformedHigh = Forall ["A"] (TyVar 1)
        malformedNegative = Forall ["A"] (TyVar (-1))
