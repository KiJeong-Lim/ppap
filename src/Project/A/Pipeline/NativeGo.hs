module Project.A.Pipeline.NativeGo
    ( NativeOutcome (..)
    , runNativeGo
    ) where

import System.FilePath
import System.Directory

import Project.A.Pipeline.Config
import Project.A.Types
import Project.A.Util.Process

data NativeOutcome = NativeOutcome
    { noGofmtLog :: ProcessLog
    , noBuildLog :: ProcessLog
    , noRunLog :: Maybe ProcessLog
    , noResult :: Either ProcessLog Obs
    } deriving (Eq, Show)

runNativeGo :: RunConfig -> FilePath -> RuntimeInput -> IO NativeOutcome
runNativeGo config caseDir input = do
    let timeouts = cfgTimeouts config
    goEnv <- nativeToolEnv caseDir
    gofmtResult <- runTimedProcess (timeoutGofmt timeouts) (Just caseDir) goEnv "gofmt" ["-w", "gofile.go"] ""
    if not (processSucceeded gofmtResult)
        then
            return
                NativeOutcome
                    { noGofmtLog = processLog gofmtResult
                    , noBuildLog = processLog gofmtResult
                    , noRunLog = Nothing
                    , noResult = Left (processLog gofmtResult)
                    }
        else do
            buildResult <-
                runTimedProcess
                    (timeoutGoBuild timeouts)
                    (Just caseDir)
                    goEnv
                    "go"
                    ["build", "-o", "native" </> "gofile-bin", "gofile.go"]
                    ""
            if not (processSucceeded buildResult)
                then
                    return
                        NativeOutcome
                            { noGofmtLog = processLog gofmtResult
                            , noBuildLog = processLog buildResult
                            , noRunLog = Nothing
                            , noResult = Left (processLog buildResult)
                            }
                else do
                    runResult <-
                        runTimedProcess
                            (timeoutNativeRun timeouts)
                            (Just caseDir)
                            (riEnv input)
                            ("." </> "native" </> "gofile-bin")
                            (riArgs input)
                            (riStdin input)
                    return
                        NativeOutcome
                            { noGofmtLog = processLog gofmtResult
                            , noBuildLog = processLog buildResult
                            , noRunLog = Just (processLog runResult)
                            , noResult = Right (obsFromProcess runResult)
                            }

nativeToolEnv :: FilePath -> IO [(String, String)]
nativeToolEnv caseDir = do
    cacheDir <- makeAbsolute (caseDir </> "go-cache")
    createDirectoryIfMissing True cacheDir
    return [("GOCACHE", cacheDir)]
