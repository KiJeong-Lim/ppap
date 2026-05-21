module Project.A.Fuzz.Corpus where

import Control.Monad
import Data.Char
import qualified Data.List as List
import System.Directory
import System.FilePath

import Project.A.Artifact
import Project.A.Fuzz.Score
import Project.A.Go.AST
import Project.A.Go.Feature
import Project.A.Types
import qualified Project.A.Util.Json as Json

data CorpusDecision
    = CorpusDecision
    { cdAccepted :: Bool
    , cdReasons :: [CorpusReason]
    , cdFeatures :: [Feature]
    , cdFeatureSetKey :: String
    } deriving (Eq, Ord, Show)

data CorpusReason
    = CorpusNewFeature Feature
    | CorpusNewFeatureSet String
    | CorpusLowScore Int
    deriving (Eq, Ord, Show)

decideCorpusAdmission :: FilePath -> Score -> CaseReport Program -> IO CorpusDecision
decideCorpusAdmission workDir score report
    | not (corpusEligible (crStatus report)) = return (corpusDecision False [] features featureKey)
    | otherwise = do
        newFeatures <- filterMNewFeature workDir features
        newFeatureSet <- isNewFeatureSet workDir featureKey
        let lowScoreReason = maybe [] lowScoreAdmission (scoreValue score)
        let reasons = concat [map CorpusNewFeature newFeatures, if newFeatureSet then [CorpusNewFeatureSet featureKey] else [], lowScoreReason]
        return (corpusDecision (not (null reasons)) reasons features featureKey)
    where
        features = List.sort (featuresOf (tcProgram (crTestCase report)))
        featureKey = featureSetKey features

commitCorpusAdmission :: FilePath -> CorpusDecision -> CaseReport Program -> IO ()
commitCorpusAdmission workDir decision report
    | not (cdAccepted decision) = return ()
    | otherwise = do
        createDirectoryIfMissing True (corpusCasesDir workDir)
        createDirectoryIfMissing True (corpusFeatureDir workDir)
        createDirectoryIfMissing True (corpusFeatureSetDir workDir)
        copyDirectoryTree (crCaseDir report) (corpusCasesDir workDir </> takeFileName (crCaseDir report))
        mapM_ (writeFeatureMarker workDir) (cdFeatures decision)
        writeFeatureSetMarker workDir (cdFeatureSetKey decision)

writeCorpusDecision :: FilePath -> CorpusDecision -> IO ()
writeCorpusDecision caseDir decision = writeTextFile (caseDir </> "corpus.json") (corpusDecisionJson decision)

corpusDecision :: Bool -> [CorpusReason] -> [Feature] -> String -> CorpusDecision
corpusDecision accepted reasons features featureKey = CorpusDecision { cdAccepted = accepted, cdReasons = reasons, cdFeatures = features, cdFeatureSetKey = featureKey }

corpusEligible :: CaseStatus -> Bool
corpusEligible CasePass = True
corpusEligible CaseInconclusive = True
corpusEligible _ = False

filterMNewFeature :: FilePath -> [Feature] -> IO [Feature]
filterMNewFeature workDir features = filterM isNew features where
    isNew feature = not <$> doesFileExist (featureMarkerPath workDir feature)

isNewFeatureSet :: FilePath -> String -> IO Bool
isNewFeatureSet workDir featureKey = not <$> doesFileExist (featureSetMarkerPath workDir featureKey)

lowScoreAdmission :: Int -> [CorpusReason]
lowScoreAdmission score
    | score <= lowScoreThreshold = [CorpusLowScore score]
    | otherwise = []

writeFeatureMarker :: FilePath -> Feature -> IO ()
writeFeatureMarker workDir feature = writeTextFile (featureMarkerPath workDir feature) ""

writeFeatureSetMarker :: FilePath -> String -> IO ()
writeFeatureSetMarker workDir featureKey = writeTextFile (featureSetMarkerPath workDir featureKey) ""

featureSetKey :: [Feature] -> String
featureSetKey [] = "none"
featureSetKey features = sanitizeKey (List.intercalate "-" (map show features))

sanitizeKey :: String -> String
sanitizeKey = map sanitizeChar where
    sanitizeChar ch
        | isAlphaNum ch = ch
        | ch `elem` "-_" = ch
        | otherwise = '-'

featureMarkerPath :: FilePath -> Feature -> FilePath
featureMarkerPath workDir feature = corpusFeatureDir workDir </> show feature

featureSetMarkerPath :: FilePath -> String -> FilePath
featureSetMarkerPath workDir featureKey = corpusFeatureSetDir workDir </> featureKey

corpusCasesDir :: FilePath -> FilePath
corpusCasesDir workDir = workDir </> "corpus" </> "cases"

corpusFeatureDir :: FilePath -> FilePath
corpusFeatureDir workDir = workDir </> "corpus" </> "by-feature"

corpusFeatureSetDir :: FilePath -> FilePath
corpusFeatureSetDir workDir = workDir </> "corpus" </> "feature-sets"

corpusDecisionJson :: CorpusDecision -> String
corpusDecisionJson decision = Json.object
    [ Json.field "accepted" (Json.bool (cdAccepted decision))
    , Json.field "reasons" (Json.list (Json.string . show) (cdReasons decision))
    , Json.field "features" (Json.list (Json.string . show) (cdFeatures decision))
    , Json.field "featureSet" (Json.string (cdFeatureSetKey decision))
    ]

lowScoreThreshold :: Int
lowScoreThreshold = 80
