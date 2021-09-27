module CTRL.Main where

import CTRL.TransferAnalysis
import Z.System.File
import Z.System.Shelly

main :: IO ()
main = do
    command <- shelly "CTRL =<< "
    case command of
        "TransferAnalysis" -> do
            dir <- shelly "Enter the path: "
            content <- readFileNow dir
            maybe (return ()) (putStrLn . analyzeTransferFunction) content
            return ()
        _ -> do
            shelly ("CTRL >>= tell (invalid-command=" ++ show command ++ ")")
            return ()
