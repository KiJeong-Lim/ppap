module Project.A.Fuzz.Summary where

import Project.A.Go.AST
import Project.A.Go.Feature
import Project.A.Fuzz.Score
import Project.A.Types
import Z.Utils

data Summary
    = Summary
    { summaryCases :: Int
    , summaryPass :: Int
    , summaryDiscard :: Int
    , summaryFail :: Int
    , summaryInconclusive :: Int
    , summaryFeatures :: [(Feature, Int)]
    , summaryCounterexamples :: Int
    , summaryInteresting :: Int
    , summaryIrrelevant :: Int
    , summaryBestScore :: Maybe Int
    , summaryBestScoreCase :: Maybe FilePath
    } deriving (Eq, Ord, Show)

emptySummary :: Summary
emptySummary = Summary { summaryCases = 0, summaryPass = 0, summaryDiscard = 0, summaryFail = 0, summaryInconclusive = 0, summaryFeatures = [(feature, 0) | feature <- allFeatures], summaryCounterexamples = 0, summaryInteresting = 0, summaryIrrelevant = 0, summaryBestScore = Nothing, summaryBestScoreCase = Nothing }

addReport :: Summary -> CaseReport Program -> Summary
addReport summary report
    = addScore report (case crStatus report of
        CasePass -> bump (\s -> s { summaryPass = summaryPass s + 1 })
        CaseDiscard -> bump (\s -> s { summaryDiscard = summaryDiscard s + 1 })
        CaseFail _ -> bump (\s -> s { summaryFail = summaryFail s + 1 })
        CaseInconclusive -> bump (\s -> s { summaryInconclusive = summaryInconclusive s + 1 }))
    where
        bump f = f (summary { summaryCases = summaryCases summary + 1, summaryFeatures = addFeatures (featuresOf (tcProgram (crTestCase report))) (summaryFeatures summary) })

renderSummary :: Summary -> String
renderSummary = withZero . showSummary

showSummary :: Summary -> ShowS
showSummary summary = strcat
    [ strstr "cases: " . shows (summaryCases summary) . nl
    , strstr "pass: " . shows (summaryPass summary) . nl
    , strstr "discard: " . shows (summaryDiscard summary) . nl
    , strstr "fail: " . shows (summaryFail summary) . nl
    , strstr "inconclusive: " . shows (summaryInconclusive summary) . nl
    , nl
    , strstr "score summary:" . nl
    , strstr "  counterexamples: " . shows (summaryCounterexamples summary) . nl
    , strstr "  interesting: " . shows (summaryInteresting summary) . nl
    , strstr "  irrelevant: " . shows (summaryIrrelevant summary) . nl
    , strstr "  best: " . showBestScore summary . nl
    , nl
    , strstr "feature coverage:" . nl
    , strcat [ showFeatureLine (summaryCases summary) feature count | (feature, count) <- summaryFeatures summary ]
    ]

addScore :: CaseReport Program -> Summary -> Summary
addScore report summary
    = case scoreOfReport report of
        FoundCounterexample _ -> recordBest 0 (summary { summaryCounterexamples = summaryCounterexamples summary + 1 })
        Interesting n _ -> recordBest n (summary { summaryInteresting = summaryInteresting summary + 1 })
        Irrelevant -> summary { summaryIrrelevant = summaryIrrelevant summary + 1 }
    where
        recordBest score current
            = case summaryBestScore current of
                Nothing -> current { summaryBestScore = Just score, summaryBestScoreCase = Just (crCaseDir report) }
                Just best
                    | score < best -> current { summaryBestScore = Just score, summaryBestScoreCase = Just (crCaseDir report) }
                    | otherwise -> current

showBestScore :: Summary -> ShowS
showBestScore summary
    = case summaryBestScore summary of
        Nothing -> strstr "none"
        Just score -> shows score . maybe id (\caseDir -> strstr " " . strstr caseDir) (summaryBestScoreCase summary)

addFeatures :: [Feature] -> [(Feature, Int)] -> [(Feature, Int)]
addFeatures features = map bump where
    bump (feature, count)
        | feature `elem` features = (feature, count + 1)
        | otherwise = (feature, count)

showFeatureLine :: Int -> Feature -> Int -> ShowS
showFeatureLine total feature count = strcat
    [ strstr "  "
    , shows feature
    , strstr ": "
    , shows count
    , strstr "/"
    , shows total
    , strstr " ("
    , shows (percentage total count)
    , strstr "%)"
    , nl
    ]

percentage :: Int -> Int -> Int
percentage total count
    | total <= 0 = 0
    | otherwise = (100 * count) `div` total
