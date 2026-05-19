module Main where

import qualified Calc.Main as Calc
import qualified Hol.Main as Hol
import qualified LGS.Main as LGS
import qualified PGS.Main as PGS
import qualified TEST.Main as TEST
import Control.Monad.IO.Class
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
    | otherwise = takeFirstOf matchPrefix ["Hol", "Calc", "LGS", "PGS", "TEST"]
    where
        matchPrefix :: String -> Maybe (String, [String])
        matchPrefix cmd = go (splitAt (length cmd) str) where
            go :: (String, String) -> Maybe (String, [String])
            go (my_prefix, my_suffix) = if my_prefix == cmd then extractArgs my_suffix >>= curry return cmd else Nothing

ppap :: ShellyT ()
ppap = do
    command <- shellyM ("ppap =<< ")
    case matchCommand command of
        Nothing -> do
            shellyM ("ppap >>= tell (invalid-command=" ++ shows command ")")
            ppap
        Just ("", []) -> return ()
        Just ("Hol", args)
            | args `elem` [[], ["pretty"], ["test"]] -> do
                shellyM ("ppap >>= exec (Hol.main" ++ extraArgs args ++ ")")
                Hol.mainWithArgsM args
        Just ("Calc", []) -> do
            shellyM ("ppap >>= exec (Calc.main)")
            liftIO Calc.main
        Just ("LGS", []) -> do
            shellyM ("ppap >>= exec (LGS.main)")
            liftIO LGS.main
        Just ("PGS", []) -> do
            shellyM ("ppap >>= exec (PGS.main)")
            liftIO PGS.main
        Just ("TEST", []) -> do
            shellyM ("ppap >>= exec (TEST.main)")
            liftIO TEST.main
        Just (cmd, args) -> do
            shellyM ("ppap >>= abort (" ++ shows "unimplemented..." ")")
            return ()
  where
    extraArgs :: [String] -> String
    extraArgs [] = ""
    extraArgs args = concat [ " --" ++ arg | arg <- args ]

copyright :: ShellyT ()
copyright = do
    shellyM ("ppap> Copyright (c) 2021-2026, Kijeong Lim")
    shellyM ("ppap> All rights reserved")
    return ()

main :: IO ()
main = runShellyT $ do
    copyright
    ppap
