module Json.JsonTest where

import Json.JsonAst
import Json.JsonLexer
import Json.JsonParser
import Json.JsonViewer
import Z.System.File

jsontest :: IO ()
jsontest = do
    maybe_input <- readFileNow "src/Json/TestUnitInput1.txt"
    case maybe_input of
        Nothing -> putStrLn "cannot open the test file"
        Just input -> do
            case readjson input of
                Left err_msg -> putStrLn ("ERROR: " ++ err_msg)
                Right input_read -> do
                    let output = prettyjson input_read
                    writeFileNow "src/Json/TestUnitOutput1.txt" (output ++ "\n")
                    return ()
