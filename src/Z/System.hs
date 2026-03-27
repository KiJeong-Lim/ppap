module Z.System
    ( readFileNow
    , writeFileNow
    , matchFileDirWithExtension
    , makePathAbsolutely
    , shelly
    ) where

import Control.Applicative
import Control.Monad (join, MonadPlus (..), (>=>))
import Control.Monad.Fix
import Control.Monad.Trans.Class
import Control.Monad.Trans.Maybe
import Data.Ratio ((%))

import System.Directory
import System.Console.Pretty
import System.IO
import qualified System.Time.Extra as Extra

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
acceptCharIf condition = PM $ \str -> if null str then [] else let ch = head str in if condition ch then [(ch, tail str)] else []

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

when :: Monad m => m Bool -> m a -> m (Maybe a)
when condm actionm = do
    cond <- condm
    if cond then fmap Just actionm else return Nothing

readFileNow :: FilePath -> IO (Maybe String)
readFileNow file = do
    tmp <- when (doesFileExist file) $ do
        file_permission <- getPermissions file
        if readable file_permission
            then do
                my_handle <- openFile file ReadMode
                my_handle_is_open <- hIsOpen my_handle
                my_result <- runMaybeT $ do
                    my_handle_is_okay <- if my_handle_is_open then lift (hIsReadable my_handle) else return False
                    if my_handle_is_okay then do
                        my_content <- fix $ \get_content -> do
                            let (++) = foldr (fmap . kons) id
                            my_handle_is_eof <- lift (hIsEOF my_handle)
                            if my_handle_is_eof then
                                return ""
                            else do
                                content1 <- lift (hGetLine my_handle)
                                my_handle_is_still_okay <- lift (hIsReadable my_handle)
                                content2 <- if my_handle_is_still_okay then get_content else fail ""
                                return $! content1 ++ "\n" ++ content2
                        return $! my_content
                    else fail ""
                my_result `seq` hClose my_handle
                return my_result
        else return Nothing
    return $! join tmp

writeFileNow :: OStreamCargo a => FilePath -> a -> IO Bool
writeFileNow file_dir my_content = do
    my_handle <- openFile file_dir WriteMode
    my_handle_is_open <- hIsOpen my_handle
    my_handle_is_okay <- if my_handle_is_open then hIsWritable my_handle else return False
    if my_handle_is_okay then do
        my_handle << my_content << Flush
        hClose my_handle
        return True
    else do
        hClose my_handle
        return False

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
        cout << (if can_prettify then elaborate msg else msg) << Flush
        if not (null msg) && last msg == ' '
            then do
                bfm <- hGetBuffering stdin
                hSetBuffering stdin LineBuffering
                str <- getLine
                hSetBuffering stdin bfm
                return str 
            else do
                delay 100
                cout << endl << Flush
                return ""

delay :: Integer -> IO ()
delay = Extra.sleep . fromMilliSec where
    fromMilliSec :: Integer -> Double
    fromMilliSec ms = fromRational (ms % 1000)

