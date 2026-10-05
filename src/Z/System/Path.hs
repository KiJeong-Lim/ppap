module Z.System.Path where

import qualified System.Directory as Directory

matchFileDirWithExtension :: String -> (String, String)
matchFileDirWithExtension dir
    = case span (\ch -> ch /= '.') (reverse dir) of
        (reversed_extension, '.' : reversed_filename)
            | all (\ch -> ch /= '/' && ch /= '\\') reversed_extension -> (reverse reversed_filename, '.' : reverse reversed_extension)
        _ -> (dir, [])

makePathAbsolutely :: FilePath -> IO (Maybe FilePath)
makePathAbsolutely = fmap (uncurry go . span (\ch -> ch /= ':')) . Directory.makeAbsolute where
    go :: String -> String -> Maybe String
    go drive path
        | take 3 path == drivesuffix = return (drive ++ path)
        | take 2 path == take 2 drivesuffix = return (drive ++ drivesuffix ++ drop 2 path)
        | otherwise = Nothing
    drivesuffix :: String
    drivesuffix = ":\\\\"
