module Z.Path where

import qualified System.Path as Path
import qualified System.Path.Directory as Directory
import qualified System.Path.Windows as Windows

makePathAbsolutely :: String -> IO (Maybe String)
makePathAbsolutely = maybe (return Nothing) (fmap (Just . toString) . Directory.canonicalizePath) . fromString where
    toString :: Windows.AbsDir -> String
    toString = Windows.toString
    fromString :: String -> Maybe Windows.RelDir
    fromString = Windows.maybe
