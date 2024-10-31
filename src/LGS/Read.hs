module LGS.Read where

import Control.Applicative
import Control.Monad
import Data.Functor
import qualified Data.List as List
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import LGS.Util
import Y.Base
import Z.Text.PC

readCharSet :: PC CharSet
readCharSet = go 0 where
    go :: Int -> PC CharSet
    go 0 = mconcat
        [ List.foldl' CsDiff <$> go 1 <*> many (consumePC " \\ " *> go 2)
        , go 1
        ]
    go 1 = mconcat
        [ CsUnion <$> go 2 <* consumePC " " <*> go 1
        , go 2
        ]
    go 2 = mconcat
        [ (CsVar <$ consumePC "$") <*> smallid
        , CsSingle <$> charPC
        , CsEnum <$> charPC <* consumePC "-" <*> charPC
        , consumePC "." $> CsUniv
        , go 3
        ]
    go _ = consumePC "(" *> go 0 <* consumePC ")"

readRegEx :: PC RegEx
readRegEx = go 0 where
    suffix :: PC (RegEx -> RegEx)
    suffix = mconcat
        [ consumePC "+" $> ReDagger
        , consumePC "*" $> ReStar
        , consumePC "?" $> ReQuest
        ]
    go :: Int -> PC RegEx
    go 0 = List.foldl' ReUnion <$> go 1 <*> many (consumePC " + " *> go 1)
    go 1 = List.foldl' ReConcat <$> go 2 <*> many (consumePC " " *> go 2)
    go 2 = List.foldl' (flip ($)) <$> go 3 <*> many suffix
    go 3 = mconcat
        [ consumePC "[" *> (ReCharSet <$> readCharSet) <* consumePC "]"
        , ReWord <$> acceptQuote
        , consumePC "()" $> ReZero
        , (ReVar <$ consumePC "$") <*> largeid
        , go 4
        ]
    go _ = consumePC "(" *> go 0 <* consumePC ")"

readBlock :: PC XBlock
readBlock = mconcat
    [ do
        consumePC "\\hshead"
        skipWhite
        consumePC "{"
        lend
        hshead <- many ((indent 4 *> regexPC "[.\\'\\n']*" <* lend) <|> (lend $> ""))
        consumePC "}"
        lend
        return (HsHead hshead)
    , do
        consumePC "\\hstail"
        skipWhite
        consumePC "{"
        lend
        hstail <- many ((indent 4 *> regexPC "[.\\'\\n']*" <* lend) <|> (lend $> ""))
        consumePC "}"
        lend
        return (HsTail hstail)
    , do
        consumePC "\\define"
        skipWhite
        consumePC "$"
        csv <- smallid
        skipWhite
        consumePC "="
        skipWhite
        cs <- readCharSet
        lend
        return (CsVDef csv cs)
    , do
        consumePC "\\define"
        skipWhite
        consumePC "$"
        rev <- largeid
        skipWhite
        consumePC "="
        skipWhite
        re <- readRegEx
        lend
        return (ReVDef rev re)
    , do
        consumePC "\\xmatch"
        skipWhite
        regex <- readRegEx
        right_ctx <- mconcat
            [ do
                consumePC " +/ "
                PosRCtx <$> readRegEx
            , do
                consumePC " / "
                OddRCtx <$> readRegEx
            , return NilRCtx
            ]
        skipWhite
        consumePC ":"
        skipWhite
        maybe_hscode <- mconcat
            [ do
                consumePC "skip"
                lend
                return Nothing
            , do
                lend
                hscode <- many (indent 4 *> regexPC "[.\\'\n']*" <* lend)
                return (Just hscode)
            ]
        return (XMatch (regex, right_ctx) maybe_hscode)
    , do
        consumePC "\\target"
        skipWhite
        consumePC "{"
        lend
        indent 4 *> consumePC "token-type:"
        skipWhite
        token_type <- acceptQuote
        lend
        indent 4 *> consumePC "lexer-name:"
        skipWhite
        lexer_name <- acceptQuote
        lend
        consumePC "}"
        lend
        return $ Target
            { getTokenType = token_type
            , getLexerName = lexer_name
            }
    ]
