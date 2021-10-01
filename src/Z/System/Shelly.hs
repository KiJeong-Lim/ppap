module Z.System.Shelly where

import Control.Applicative
import Control.Monad
import System.Console.Pretty
import System.IO
import Z.Text.PM
import Z.Utils

shelly :: String -> IO String
shelly = go where
    identifierPM :: PM String
    identifierPM = pure (:) <*> acceptCharIf (\ch -> ch `elem` ['$'] ++ ['a' .. 'z'] ++ ['A' .. 'Z']) <*> many (acceptCharIf (\ch -> ch `elem` ['a' .. 'z'] ++ ['A' .. 'Z'] ++ ['0' .. '9'] ++ ['.', '_', '-']))
    numberPM :: PM String
    numberPM = mconcat
        [ pure (:) <*> acceptCharIf (\ch -> ch `elem` ['1' .. '9']) <*> many (acceptCharIf (\ch -> ch `elem` ['0' .. '9']))
        , consumeStr "0" *> pure "0"
        ]
    readDirectedBind :: PM String
    readDirectedBind = consumeStr ">>=" *> pure ">>="
    readReversedBind :: PM String
    readReversedBind = consumeStr "=<<" *> pure "=<<"
    readQuote :: PM String
    readQuote = matchPrefix "\"" *> autoPM 0
    skipWhite :: PM ()
    skipWhite = many (acceptCharIf (\ch -> ch == ' ')) *> pure ()
    litPM :: PM String
    litPM = mconcat
        [ numberPM
        , do
            quote <- readQuote
            return (color Blue (show quote))
        ]
    atomPM :: Bool -> PM String
    atomPM paren_be_colored = do
        res <- mconcat
            [ litPM
            , argPM paren_be_colored
            ]
        return (" " ++ res)
    argPM :: Bool -> PM String
    argPM paren_be_colored = do
        consumeStr "("
        skipWhite
        str <- mconcat
            [ do
                lhs <- identifierPM
                consumeStr "="
                skipWhite
                rhs <- litPM <|> argPM False
                skipWhite
                return (lhs ++ " = " ++ rhs)
            , do
                fun <- identifierPM
                skipWhite
                args <- many (atomPM False <* skipWhite)
                return (fun ++ concat args)
            , return ""
            ]
        consumeStr ")"
        let my_colorize = if paren_be_colored then color Green else id
        return (my_colorize "(" ++ str ++ my_colorize ")")
    shellPM :: PM [String]
    shellPM = do
        skipWhite
        lhs <- identifierPM
        skipWhite
        bind <- readDirectedBind <|> readReversedBind
        let my_colorize = if bind == "=<<" then color Yellow else id
        stmt <- mconcat
            [ do
                skipWhite
                fun <- identifierPM
                skipWhite
                args <- many (atomPM True <* skipWhite)
                return ([my_colorize lhs, " ", bind, " ", color Green fun] ++ args)
            , do
                skipWhite
                return ([my_colorize lhs, " ", bind, " "])
            ]
        mconcat
            [ do
                consumeStr "."
                skipWhite
                return (stmt ++ ["."])
            , return stmt
            ]
    elaborate :: String -> String
    elaborate str = maybe str concat (foldr (const . Just) Nothing [ res | (res, "") <- unPM shellPM str ])
    go :: String -> IO String
    go msg = do
        can_prettify <- supportsPretty
        let msg' = if can_prettify then elaborate msg else msg
        if not (null msg) && last msg == ' '
            then do
                putStr msg'
                hFlush stdout
                getLine
            else do
                putStrLn msg'
                return ""
