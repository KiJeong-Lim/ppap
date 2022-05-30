module Json.JsonTest where

import Json.JsonAst
import Json.JsonLexer
import Json.JsonParser
import Json.JsonViewer
import Z.System.File

jsontest :: IO ()
jsontest = do
    input <- readFileNow "src/Json/TestUnitInput1.txt"
    let output = either id showjson . readjson $ maybe (error "CANNOT READ") id input
    writeFileNow "src/Json/TestUnitOutput1.txt" output
    return ()
