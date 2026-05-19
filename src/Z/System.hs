module Z.System
    ( readFileNow
    , writeFileNow
    , matchFileDirWithExtension
    , makePathAbsolutely
    , shelly
    ) where

import Control.Applicative
import Control.Exception (finally)
import Control.Monad (MonadPlus (..), (>=>))
import Data.Ratio ((%))

import System.Directory
import System.Console.Pretty
import System.IO
import qualified System.Time.Extra as Extra

import Z.System.File (readFileNow, writeFileNow)
import Z.Utils

newtype PM a
    = PM { unPM :: ReadS a }
    deriving ()

instance Functor PM where
    fmap a2b p1 = PM $ \str0 -> [ (a2b a, str1) | (a, str1) <- unPM p1 str0 ]

instance Applicative PM where
    pure a = PM $ \str0 -> [(a, str0)]
    p1 <*> p2 = PM $ \str0 -> [ (a2b a, str2) | (a2b, str1) <- unPM p1 str0, (a, str2) <- unPM p2 str1 ]

instance Monad PM where
    -- return = PM . curry return
    p1 >>= p2 = PM (unPM p1 >=> uncurry (unPM . p2))

instance Alternative PM where
    empty = PM (pure mempty)
    p1 <|> p2 = PM (pure mappend <*> unPM p1 <*> unPM p2)

instance MonadPlus PM where

instance MonadFail PM where
    fail = const empty

instance Semigroup (PM a) where
    p1 <> p2 = p1 <|> p2

instance Monoid (PM a) where
    mempty = empty

autoPM :: Read a => Precedence -> PM a
autoPM = PM . readsPrec

acceptCharIf :: (Char -> Bool) -> PM Char
acceptCharIf condition = PM $ \str -> case str of
    ch : rest | condition ch -> [(ch, rest)]
    _ -> []

consumeStr :: String -> PM ()
consumeStr prefix = PM $ \str -> let n = length prefix in if take n str == prefix then return ((), drop n str) else []

matchPrefix :: String -> PM ()
matchPrefix prefix = PM $ \str -> let n = length prefix in if take n str == prefix then return ((), str) else []
matchFileDirWithExtension :: String -> (String, String)
matchFileDirWithExtension dir
    = case span (\ch -> ch /= '.') (reverse dir) of
        (reversed_extension, '.' : reversed_filename) -> (reverse reversed_filename, '.' : reverse reversed_extension)
        (reversed_filename, must_be_null) -> (reverse reversed_filename, [])

makePathAbsolutely :: FilePath -> IO (Maybe FilePath)
makePathAbsolutely = fmap (uncurry go . span (\ch -> ch /= ':')) . makeAbsolute where
    go :: String -> String -> Maybe String
    go drive path
        | take 3 path == drivesuffix = return (drive ++ path)
        | take 2 path == take 2 drivesuffix = return (drive ++ drivesuffix ++ drop 2 path)
        | otherwise = Nothing
    drivesuffix :: String
    drivesuffix = ":\\\\"

shelly :: String -> IO String
shelly = shellymain where
    identifierPM :: PM String
    identifierPM = pure (:) <*> acceptCharIf (\ch -> ch `elem` ['$'] ++ ['a' .. 'z'] ++ ['A' .. 'Z']) <*> many (acceptCharIf (\ch -> ch `elem` ['a' .. 'z'] ++ ['A' .. 'Z'] ++ ['0' .. '9'] ++ ['.', '_', '-']))
    numberPM :: PM String
    numberPM = (pure (:) <*> acceptCharIf (\ch -> ch `elem` ['1' .. '9']) <*> many (acceptCharIf (\ch -> ch `elem` ['0' .. '9']))) <|> (consumeStr "0" *> pure "0")
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
        res <- litPM <|> argPM paren_be_colored
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
            , litPM
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
        let my_colorize = modifySep '.' one (if bind == "=<<" then color Yellow else color Green)
        stmt <- mconcat
            [ do
                skipWhite
                fun <- identifierPM
                skipWhite
                args <- many (atomPM True <* skipWhite)
                return ([my_colorize lhs, " ", bind, " ", color Green fun] ++ args)
            , return [my_colorize lhs, " ", bind, " "]
            ]
        skipWhite
        mconcat
            [ do
                consumeStr "."
                return (stmt ++ ["."])
            , return stmt
            ]
    smallshell :: String -> String
    smallshell str = case span (\ch -> ch /= '>') str of
        (my_prefix, my_suffix) -> case span (\ch -> ch == '>') my_suffix of
            (my_suffix_left, my_suffix_right) -> if null my_suffix_left then my_prefix ++ my_suffix_left ++ my_suffix_right else color Cyan (my_prefix ++ my_suffix_left) ++ my_suffix_right
    elaborate :: String -> String
    elaborate str = maybe (smallshell str) concat (foldr (const . Just) Nothing [ res | (res, "") <- unPM shellPM str ])
    shellymain :: String -> IO String
    shellymain msg = do
        can_prettify <- supportsPretty
        let rendered = if can_prettify then elaborate msg else msg
        cout << rendered << Flush
        if not (null msg) && last msg == ' '
            then do
                is_terminal <- hIsTerminalDevice stdin
                if is_terminal
                    then readEditedLine rendered
                    else do
                        bfm <- hGetBuffering stdin
                        hSetBuffering stdin LineBuffering
                        str <- getLine
                        hSetBuffering stdin bfm
                        return str
            else do
                delay 100
                cout << endl << Flush
                return ""
    readEditedLine :: String -> IO String
    readEditedLine prompt = do
        bfm <- hGetBuffering stdin
        echo <- hGetEcho stdin
        hSetBuffering stdin NoBuffering
        hSetEcho stdin False
        let restore = do
                hSetEcho stdin echo
                hSetBuffering stdin bfm
        loop "" "" `finally` restore
      where
        loop :: String -> String -> IO String
        loop left right = do
            ch <- hGetChar stdin
            case ch of
                '\n' -> finish left right
                '\r' -> finish left right
                '\DEL' -> backspace left right
                '\b' -> backspace left right
                '\ESC' -> do
                    (left', right') <- escape left right
                    loop left' right'
                _ | ch >= ' ' -> do
                    let left' = left ++ [ch]
                    redraw left' right
                    loop left' right
                  | otherwise -> loop left right
        finish left right = do
            cout << endl << Flush
            return (left ++ right)
        backspace [] right = loop [] right
        backspace left right = do
            let left' = init left
            redraw left' right
            loop left' right
        escape left right = do
            ready <- hReady stdin
            if not ready
                then return (left, right)
                else do
                    ch <- hGetChar stdin
                    case ch of
                        '[' -> csi left right
                        'O' -> ss3 left right
                        _ -> return (left, right)
        csi left right = do
            ready <- hReady stdin
            if not ready
                then return (left, right)
                else do
                    ch <- hGetChar stdin
                    case ch of
                        'D' -> moveLeft left right
                        'C' -> moveRight left right
                        'A' -> return (left, right)
                        'B' -> return (left, right)
                        'H' -> moveHome left right
                        'F' -> moveEnd left right
                        '3' -> do
                            tilde <- hReady stdin
                            if tilde then do { _ <- hGetChar stdin; deleteChar left right } else return (left, right)
                        '1' -> consumeTilde *> moveHome left right
                        '4' -> consumeTilde *> moveEnd left right
                        _ -> return (left, right)
        ss3 left right = do
            ready <- hReady stdin
            if not ready
                then return (left, right)
                else do
                    ch <- hGetChar stdin
                    case ch of
                        'H' -> moveHome left right
                        'F' -> moveEnd left right
                        _ -> return (left, right)
        consumeTilde = do
            ready <- hReady stdin
            if ready then do { _ <- hGetChar stdin; return () } else return ()
        moveLeft [] right = return ([], right)
        moveLeft left right = do
            let left' = init left
                right' = last left : right
            redraw left' right'
            return (left', right')
        moveRight left [] = return (left, [])
        moveRight left (ch : right) = do
            let left' = left ++ [ch]
            redraw left' right
            return (left', right)
        moveHome left right = do
            redraw "" (left ++ right)
            return ("", left ++ right)
        moveEnd left right = do
            redraw (left ++ right) ""
            return (left ++ right, "")
        deleteChar left [] = return (left, [])
        deleteChar left (_ : right) = do
            redraw left right
            return (left, right)
        redraw left right = do
            cout << "\r\ESC[2K" << prompt << left << right << cursorBack (length right) << Flush
        cursorBack 0 = ""
        cursorBack n = "\ESC[" ++ show n ++ "D"

delay :: Integer -> IO ()
delay = Extra.sleep . fromMilliSec where
    fromMilliSec :: Integer -> Double
    fromMilliSec ms = fromRational (ms % 1000)
