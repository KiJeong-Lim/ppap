module Isa.Dep where

import Control.Applicative
import Control.Monad
import Data.IORef
import qualified Data.List as List
import qualified Data.Set as Set
import qualified Data.Map.Strict as Map
import qualified System.Directory as Directory
import System.FilePath
import Y.Base
import Z.Text.PC
import Z.System.Shelly
import Z.System.File
import Z.System.Path
import Z.Utils

l4v :: FilePath
l4v = "l4v/"

loadthys :: IO (Map.Map FilePath FilePath)
loadthys = do
    files <- findThyFiles l4v
    return $ Map.fromList [(takeFileName f, f) | f <- files]
  where
    findThyFiles :: FilePath -> IO [FilePath]
    findThyFiles dir = do
        exists <- Directory.doesDirectoryExist dir
        if not exists
            then return []
            else do
                contents <- Directory.listDirectory dir
                let fullPaths = map (dir </>) contents
                files <- filterM Directory.doesFileExist fullPaths
                dirs <- filterM Directory.doesDirectoryExist fullPaths
                let thyFiles = filter (\f -> takeExtension f == ".thy") files
                subFiles <- concat <$> mapM findThyFiles dirs
                return (thyFiles ++ subFiles)

readimports :: FilePath -> IO (Either String [FilePath])
readimports pth = go where
    go :: IO (Either String [FilePath])
    go = do
        src <- readFileNow pth
        case src of
            Nothing -> return (Left "cannot open the file")
            Just src -> return (runPC pth parser src)
    id :: PC String
    id = negPC (consumePC "begin") *> regexPC "['A'-'Z' 'a'-'z'] ['A'-'Z' 'a'-'z' '_' '0'-'9']*"
    qualid :: PC String
    qualid = do
        hd <- id
        tl <- many $ do
            consumePC "."
            id
        return (last (hd : tl))
    quoteid :: PC String
    quoteid = do
        q <- acceptQuote
        return $! last (splitBy '.' q)
    cat :: String -> String -> String
    x `cat` y = y
    skipComment :: PC ()
    skipComment = do
        skipSpace
        many $ do
            regexPC "\"(*\" ([.\\\'*\'] + \"*\" [.\\\')\'])* \"*)\""
            skipSpace
        many $ do
            regexPC "\"text \\\\<open>\" [.\\\'\\\\\']* \"\\\\<close>\""
            skipSpace
        skipSpace
        return ()
    parser :: PC [String]
    parser = do
        skipComment
        consumePC "theory"
        skipSpace
        id
        skipComment
        consumePC "imports"
        skipComment
        res <- many $ do
            it <- qualid <> quoteid
            skipComment
            return it
        skipComment
        consumePC "begin"
        endPC
        return res

testreadimports :: IO ()
testreadimports = do
    imps <- readimports (l4v ++ "proof/infoflow/ADT_IF.thy")
    case imps of
        Left err -> putStrLn err
        Right res -> print res

findDep :: [FilePath] -> FilePath -> IO [(FilePath, FilePath)]
findDep pths pth
    | pth == "Main" = return []
    | pth `elem` pths = return [(pth, pth)]
    | otherwise = do
        m <- loadthys
        imps <- case pth `Map.lookup` m of
            Nothing -> return (Left ("error=" ++ show pth))
            Just cur -> readimports cur
        case imps of
            Left err -> return []
            Right imps -> do
                res <- concat <$> mapM (findDep pths) [ pth ++ ".thy" | pth <- imps ]
                return [ (pth, tgt) | (src, tgt) <- res ]

main :: IO ()
main = do
    list <- readFileNow "list.txt"
    case list of
        Nothing -> putStrLn "cannot find \"list.txt\""
        Just list -> do
            let thys = splitBy '\n' list
            thys <- return $! map takeFileName $! filter (not . null) thys
            sequence_
                [ do
                    out <- findDep (thys List.\\ [thy]) (takeFileName thy)
                    print (List.nub out)
                | thy <- thys
                ]
