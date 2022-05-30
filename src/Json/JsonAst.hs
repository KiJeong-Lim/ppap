module Json.JsonAst where

import Control.Monad
import Json.JsonLexer
import Json.JsonParser

type PErrMsg = String

readjson :: String -> Either PErrMsg Value
readjson = lexInput >=> parseInput where
    lexInput :: String -> Either PErrMsg [JsonToken]
    lexInput = either (uncurry $ \row -> \col -> Left $ "lexing-error at row = " ++ shows row (", col = " ++ shows col "")) Right . jsonlexer
    parseInput :: [JsonToken] -> Either PErrMsg Value
    parseInput = either (Left . maybe "parsing-error at EOF" (\tok -> "parsing-error at " ++ shows tok "")) Right . jsonparser
