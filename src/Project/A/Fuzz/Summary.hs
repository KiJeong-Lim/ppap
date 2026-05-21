module Project.A.Fuzz.Summary where

import Project.A.Go.AST
import Project.A.Go.Feature
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
    } deriving (Eq, Ord, Show)

emptySummary :: Summary
emptySummary = Summary { summaryCases = 0, summaryPass = 0, summaryDiscard = 0, summaryFail = 0, summaryInconclusive = 0, summaryFeatures = [(feature, 0) | feature <- allFeatures] }

addReport :: Summary -> CaseReport Program -> Summary
addReport summary report
    = case crStatus report of
        CasePass -> bump (\s -> s { summaryPass = summaryPass s + 1 })
        CaseDiscard -> bump (\s -> s { summaryDiscard = summaryDiscard s + 1 })
        CaseFail _ -> bump (\s -> s { summaryFail = summaryFail s + 1 })
        CaseInconclusive -> bump (\s -> s { summaryInconclusive = summaryInconclusive s + 1 })
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
    , strstr "feature coverage:" . nl
    , strcat [ showFeatureLine (summaryCases summary) feature count | (feature, count) <- summaryFeatures summary ]
    ]

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
