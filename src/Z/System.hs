module Z.System
    ( readFileNow
    , writeFileNow
    , matchFileDirWithExtension
    , makePathAbsolutely
    , ShellyState
    , ShellyT
    , emptyShellyState
    , runShellyT
    , shellyM
    , shelly
    ) where

import Control.Applicative
import Control.Exception (finally)
import Control.Monad (MonadPlus (..), (>=>))
import Control.Monad.IO.Class
import Control.Monad.Trans.State.Strict
import Data.Ratio ((%))

import System.Directory
import System.Console.Pretty
import System.IO
import qualified System.Time.Extra as Extra

import Z.System.File (readFileNow, writeFileNow)
import Z.Utils

data ShellyState = ShellyState
    { shellyHistory :: [String]
    } deriving ()

type ShellyT = StateT ShellyState IO

emptyShellyState :: ShellyState
emptyShellyState = ShellyState { shellyHistory = [] }

runShellyT :: ShellyT a -> IO a
runShellyT action = evalStateT action emptyShellyState

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
shelly msg = runShellyT (shellyM msg)

shellyM :: String -> ShellyT String
shellyM = shellymain where
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
    shellymain :: String -> ShellyT String
    shellymain msg = do
        can_prettify <- liftIO supportsPretty
        let rendered = if can_prettify then elaborate msg else msg
        liftIO $ cout << rendered << Flush
        if not (null msg) && last msg == ' '
            then do
                is_terminal <- liftIO (hIsTerminalDevice stdin)
                if is_terminal
                    then readEditedLine rendered
                    else do
                        bfm <- liftIO (hGetBuffering stdin)
                        liftIO (hSetBuffering stdin LineBuffering)
                        str <- liftIO getLine
                        liftIO (hSetBuffering stdin bfm)
                        remember str
                        return str
            else do
                liftIO (delay 100)
                liftIO $ cout << endl << Flush
                return ""
    readEditedLine :: String -> ShellyT String
    readEditedLine prompt = do
        history <- gets shellyHistory
        bfm <- liftIO (hGetBuffering stdin)
        echo <- liftIO (hGetEcho stdin)
        liftIO (hSetBuffering stdin NoBuffering)
        liftIO (hSetEcho stdin False)
        let restore = do
                hSetEcho stdin echo
                hSetBuffering stdin bfm
        str <- liftIO (loop history 0 "" "" Nothing `finally` restore)
        remember str
        return str
      where
        loop :: [String] -> Int -> String -> String -> Maybe String -> IO String
        loop history index left right saved = do
            ch <- hGetChar stdin
            case ch of
                '\n' -> finish left right
                '\r' -> finish left right
                '\DEL' -> backspace history index left right saved
                '\b' -> backspace history index left right saved
                '\ESC' -> do
                    (index', left', right', saved') <- escape history index left right saved
                    loop history index' left' right' saved'
                _ | ch >= ' ' -> do
                    let left' = left ++ [ch]
                    redraw left' right
                    loop history index left' right saved
                  | otherwise -> loop history index left right saved
        finish left right = do
            cout << endl << Flush
            return (left ++ right)
        backspace history index [] right saved = loop history index [] right saved
        backspace history index left right saved = do
            let left' = init left
            redraw left' right
            loop history index left' right saved
        escape history index left right saved = do
            ready <- hReady stdin
            if not ready
                then return (index, left, right, saved)
                else do
                    ch <- hGetChar stdin
                    case ch of
                        '[' -> csi history index left right saved
                        'O' -> ss3 index left right saved
                        _ -> return (index, left, right, saved)
        csi history index left right saved = do
            ready <- hReady stdin
            if not ready
                then return (index, left, right, saved)
                else do
                    ch <- hGetChar stdin
                    case ch of
                        'D' -> withIndex index saved <$> moveLeft left right
                        'C' -> withIndex index saved <$> moveRight left right
                        'A' -> historyUp history index left right saved
                        'B' -> historyDown history index left right saved
                        'H' -> withIndex index saved <$> moveHome left right
                        'F' -> withIndex index saved <$> moveEnd left right
                        '3' -> do
                            tilde <- hReady stdin
                            if tilde then do { _ <- hGetChar stdin; withIndex index saved <$> deleteChar left right } else return (index, left, right, saved)
                        '1' -> consumeTilde *> (withIndex index saved <$> moveHome left right)
                        '4' -> consumeTilde *> (withIndex index saved <$> moveEnd left right)
                        _ -> return (index, left, right, saved)
        ss3 index left right saved = do
            ready <- hReady stdin
            if not ready
                then return (index, left, right, saved)
                else do
                    ch <- hGetChar stdin
                    case ch of
                        'H' -> withIndex index saved <$> moveHome left right
                        'F' -> withIndex index saved <$> moveEnd left right
                        _ -> return (index, left, right, saved)
        consumeTilde = do
            ready <- hReady stdin
            if ready then do { _ <- hGetChar stdin; return () } else return ()
        withIndex index saved (left, right) = (index, left, right, saved)
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
        historyUp [] index left right saved = return (index, left, right, saved)
        historyUp history index left right saved
            | index >= length history = return (index, left, right, saved)
            | otherwise = do
                let saved' = case saved of
                        Nothing -> Just (left ++ right)
                        Just old -> Just old
                    entry = history !! index
                redraw entry ""
                return (index + 1, entry, "", saved')
        historyDown history index left right saved
            | index <= 0 = return (index, left, right, saved)
            | index == 1 = do
                let entry = maybe "" id saved
                redraw entry ""
                return (0, entry, "", saved)
            | otherwise = do
                let index' = index - 1
                    entry = history !! (index' - 1)
                redraw entry ""
                return (index', entry, "", saved)
        redraw left right = do
            cout << "\r\ESC[2K" << prompt << left << right << cursorBack (length right) << Flush
        cursorBack 0 = ""
        cursorBack n = "\ESC[" ++ show n ++ "D"
    remember :: String -> ShellyT ()
    remember str = do
        let entry = dropWhile (== ' ') str
        if null entry
            then return ()
            else modify $ \st -> st { shellyHistory = entry : filter (/= entry) (shellyHistory st) }

delay :: Integer -> IO ()
delay = Extra.sleep . fromMilliSec where
    fromMilliSec :: Integer -> Double
    fromMilliSec ms = fromRational (ms % 1000)
