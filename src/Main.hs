module Main where

import qualified Aladdin.Main as Aladdin
import qualified Calc.Main as Calc
import qualified LGS.Main as LGS
import qualified PGS.Main as PGS
import qualified TEST.Main as TEST
import Z.Algo.Function
import Z.System.Shelly
import Z.Utils

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
    | otherwise = foldr (/>) Nothing (map matchPrefix ["Aladdin", "Calc", "LGS", "PGS", "TEST"])
    where
        matchPrefix :: String -> Maybe (String, [String])
        matchPrefix pre = do
            let n = length pre
            args <- if pre == take n str
                then extractArgs (drop n str)
                else Nothing
            return (pre, args)

ppap :: IO ()
ppap = do
    command <- shelly "ppap =<< "
    case matchCommand command of
        Just ("", []) -> do
            shelly "ppap >>= quit"
            return ()
        Just ("Aladdin", []) -> do
            shelly "ppap >>= exec (Aladdin.main)"
            Aladdin.main
        Just ("Calc", []) -> do
            shelly "ppap >>= exec (Calc.main)"
            Calc.main
        Just ("Calc", ["quick"]) -> do
            shelly "ppap >>= eval (Calc.runCalc \"calc-example1.calc\")"
            Calc.runCalc "calc-example1.calc"
            shelly "ppap >>= quit"
            return ()
        Just ("LGS", []) -> do
            shelly "ppap >>= exec (LGS.main)"
            LGS.main
        Just ("LGS", ["quick"]) -> do
            shelly "ppap >>= eval (LGS.runLGS \"src/Aladdin/Front/Analyzer/Lexer\")"
            LGS.runLGS "src/Aladdin/Front/Analyzer/Lexer"
            shelly "ppap >>= quit"
            return ()
        Just ("PGS", []) -> do
            shelly "ppap >>= exec (PGS.main)"
            PGS.main
        Just ("PGS", ["quick"]) -> do
            shelly "ppap >>= eval (PGS.runPGS \"src/Aladdin/Front/Analyzer/Parser\")"
            PGS.runPGS "src/Aladdin/Front/Analyzer/Parser"
            shelly "ppap >>= quit"
            return ()
        Just ("TEST", []) -> do
            shelly "ppap >>= exec (TEST.main)"
            TEST.main
        invalid_command -> do
            shelly ("ppap >>= tell (invalid-command=" ++ show invalid_command ++ ")")
            shelly "ppap >>= quit"
            return ()

main :: IO ()
main = do
    putStrLn "Copyright (c) 2021, Kijeong Lim"
    ppap
    return ()
