module Main where

import qualified Aladdin.Main as Aladdin
import qualified Calc.Main as Calc
import qualified Genie.Main as Genie
import qualified Jasmine.Main as Jasmine
import qualified LGS.Main as LGS
import qualified PGS.Main as PGS
import Z.Algo.Function
import Z.System.Shelly

extractArgs :: String -> Maybe [String]
extractArgs args_rep
    | take 2 args_rep == "--"
    = case span (\ch -> ch /= ' ') (drop 2 args_rep) of
        (arg, next_args_rep) -> do
            next_args <- extractArgs next_args_rep
            return (arg : next_args)
    | otherwise
    = case args_rep of
        [] -> return []
        ' ' : next_args_rep -> extractArgs next_args_rep
        _ -> Nothing

matchCommand :: String -> Maybe (String, [String])
matchCommand str
    | null str = return ("", [])
    | otherwise = takeFirstOf matchPrefix ["Aladdin", "Calc", "LGS", "PGS", "TEST"]
    where
        matchPrefix :: String -> Maybe (String, [String])
        matchPrefix cmd = go (splitAt (length cmd) str) where
            go :: (String, String) -> Maybe (String, [String])
            go (my_prefix, my_suffix) = if my_prefix == cmd then extractArgs my_suffix >>= curry return cmd else Nothing

ppap :: IO ()
ppap = do
    command <- shelly ("ppap =<< ")
    case matchCommand command of
        Nothing -> do
            shelly ("ppap >>= tell (invalid-command=" ++ shows command ")")
            ppap
        Just ("", []) -> return ()
        Just ("Aladdin", []) -> do
            shelly ("ppap >>= exec (Aladdin.main)")
            Aladdin.main
        Just ("Calc", []) -> do
            shelly ("ppap >>= exec (Calc.main)")
            Calc.main
        Just ("Genie", []) -> do
            shelly ("ppap >>= exec (Genie.main)")
            Genie.main
        Just ("Jasmine", []) -> do
            shelly ("ppap >>= exec (Jasmine.main)")
            Jasmine.main
        Just ("LGS", []) -> do
            shelly ("ppap >>= exec (LGS.main)")
            LGS.main
            -- src/Aladdin/Front/Analyzer/Lexer.txt
        Just ("PGS", []) -> do
            shelly ("ppap >>= exec (PGS.main)")
            PGS.main
            -- src/Aladdin/Front/Analyzer/Parser.txt
        Just (cmd, args) -> do
            shelly ("ppap >>= abort (" ++ shows "unimplemented..." ")")
            return ()

copyright :: IO ()
copyright = do
    shelly ("ppap> Copyright (c) 2021-2024, Kijeong Lim")
    shelly ("ppap> All rights reserved")
    return ()

main :: IO ()
main = do
    copyright
    ppap
