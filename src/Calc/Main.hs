module Calc.Main where

import Calc.ControlSystem.Export
import Control.Monad
import Control.Monad.Trans.Except
import System.IO
import Z.Text.Doc
import Z.Text.PM
import Z.System.File
import Z.System.Path
import Z.System.Shelly
import Z.Utils

calculatorstring :: String
calculatorstring = "calculator> "

execQuery :: String -> ExceptT String IO Doc
execQuery = go . preprocessor where
    preprocessor :: String -> String
    preprocessor = id
    go :: String -> ExceptT String IO Doc
    go txt = return (pstr txt)

runCalc :: String -> IO ()
runCalc file_dir = do
    content <- readFileNow file_dir
    case content of
        Nothing -> do
            cout << "*** cannot open your file, file-path = " ++ shows file_dir "." << endl
            return ()
        Just query -> do
            res <- runExceptT (execQuery query)
            case res of
                Left err_msg -> do
                    cout << err_msg << endl
                    return ()
                Right output -> do
                    good_recorded <- writeFileNow (file_dir ++ ".output") output
                    if good_recorded
                        then do
                            shelly (calculatorstring ++ "Jobs finished.")
                            return ()
                        else do
                            cout << output << endl
                            return ()

main :: IO ()
main = do
    dir <- shelly ("Calc =<< ")
    runCalc dir
    shelly ("Calc >>= quit")
    return ()
