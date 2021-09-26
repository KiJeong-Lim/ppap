module Z.System.Path where

import qualified System.Path as Path
import qualified System.Path.Directory as Directory
import qualified System.Path.Windows as Windows

matchFileDirWithExtension :: String -> (String, String)
matchFileDirWithExtension dir
    = case span (\ch -> ch /= '.') (reverse dir) of
        (reversed_extension, '.' : reversed_filename) -> (reverse reversed_filename, '.' : reverse reversed_extension)
        (reversed_filename, must_be_null) -> (reverse reversed_filename, [])

makePathAbsolutely :: String -> IO (Maybe String)
makePathAbsolutely = maybe (return Nothing) (fmap (Just . toString) . Directory.canonicalizePath) . fromString where
    toString :: Windows.AbsDir -> String
    toString = Windows.toString
    fromString :: String -> Maybe Windows.RelDir
    fromString = Windows.maybe
