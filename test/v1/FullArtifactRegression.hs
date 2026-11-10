module Main where

import Control.Monad
import Data.Either (isLeft, isRight)
import Data.Int
import qualified Data.IntMap.Strict as IntMap
import Data.List (intercalate)
import qualified Data.Map.Strict as Map
import Data.Maybe (isNothing)
import Hol.BETA.Constant
import Hol.BETA.Header
import Hol.V1.FullBytecode
import Text.Read (readMaybe)
import Z.Utils (Unique (..))

check :: String -> Bool -> IO ()
check label condition = unless condition (ioError (userError label))

artifact :: String -> String -> String -> String -> String -> String
artifact version words symbols variables metadata = unwords ["FullArtifact", version, words, symbols, variables, metadata, "[] [] []"]

main :: IO ()
main = do
    let words = "[1213156401,2,1,2,0,0,0,0,3,21,1,0,0,0,0,-1]"
        symbols = "[SSConstant (SCLogical 2),SSConstant (SCBuiltin 2)]"
        minimal = artifact "2" words symbols "[]" "[]"
        modulus = 2 * (toInteger (maxBound :: Int) + 1)
        invalidExecutable =
            [ artifact (show (modulus + 2)) words symbols "[]" "[]"
            , artifact "2" ("[" ++ show (2 ^ (64 :: Int) + 1213156401) ++ ",2,1,2,0,0,0,0,3,21,1,0,0,0,0,-1]") symbols "[]" "[]"
            , artifact "2" words ("[SSConstant (SCLogical 2),SSConstant (SCBuiltin " ++ show (modulus + 2) ++ ")]") "[]" "[]"
            ]
    base <- either (ioError . userError) return (deserializeFullBytecode minimal)
    forM_ invalidExecutable $ \source -> check "overflow must not wrap into an executable full artifact" (isLeft (deserializeFullBytecode source))
    check "full artifact trailing junk is rejected" (isLeft (deserializeFullBytecode (minimal ++ " junk")))
    check "valid noncanonical full artifact Read notation remains supported" (isRight (deserializeFullBytecode (" (FullArtifact (0x2) [0x484f4c31,2,1,2,0,0,0,0,3,21,1,0,0,0,0,-1] [SSConstant (SCLogical (0x2)),SSConstant (SCBuiltin (0x2))] [] [] [] [] []) ")))

    let overflows = [show (toInteger (maxBound :: Int) + 1), show (toInteger (minBound :: Int) - 1), "0x10000000000000000", "-0x10000000000000000"]
        withSymbol symbol = artifact "2" "[]" ("[" ++ symbol ++ "]") "[]" "[]"
        withVariable variable = artifact "2" "[]" "[]" ("[" ++ variable ++ "]") "[]"
        withType typ = artifact "2" "[]" "[]" "[]" ("[(Nothing,Just (" ++ typ ++ "),Nothing)]")
        locations value =
            [ "Just ((" ++ intercalate "," (take 2 fields) ++ "),(" ++ intercalate "," (drop 2 fields) ++ "))"
            | index <- [0 :: Int .. 3]
            , let fields = [if field == index then value else "1" | field <- [0 .. 3]]
            ]
        metadataCases value =
            [ artifact ("(" ++ value ++ ")") "[]" "[]" "[]" "[]"
            , withSymbol ("SSConstant (SCDataUnique (" ++ value ++ ") Nothing)")
            , withSymbol ("SSConstant (SCTypeUnique (" ++ value ++ "))")
            , withSymbol ("SSConstant (SCBuiltin (" ++ value ++ "))")
            , withSymbol ("SSConstant (SCLogical (" ++ value ++ "))")
            , withVariable ("SVGenerated (" ++ value ++ ") Nothing")
            , withVariable ("SVType (" ++ value ++ ")")
            , withType ("STVar (" ++ value ++ ")")
            , withType ("STMeta (" ++ value ++ ")")
            , withSymbol ("SSPresburger (SFRelation (" ++ value ++ ") SPZero SPZero) [] Nothing")
            , withSymbol ("SSPresburger (SFConnect (" ++ value ++ ") (SFTruth True) (SFTruth False)) [] Nothing")
            ] ++ concat
                [ [withSymbol ("SSPresburger (SFTruth True) [] (" ++ location ++ ")"), artifact "2" "[]" "[]" "[]" ("[(Nothing,Nothing," ++ location ++ ")]")]
                | location <- locations value
                ]
    forM_ overflows $ \value -> forM_ (metadataCases value) $ \source ->
        check ("bounded full artifact metadata must reject overflow: " ++ source) (isNothing (readMaybe source :: Maybe FullArtifact))
    forM_ [show (toInteger (maxBound :: Int64) + 1), show (toInteger (minBound :: Int64) - 1)] $ \value ->
        check "full artifact words reject overflow" (isNothing (readMaybe (artifact "2" ("[" ++ value ++ "]") "[]" "[]" "[]") :: Maybe FullArtifact))

    let boundaries = FullArtifact maxBound [minBound, maxBound] [SSConstant (SCDataUnique minBound Nothing), SSConstant (SCTypeUnique maxBound)] [SVGenerated minBound Nothing, SVType maxBound] [(Nothing, Just (STMeta minBound), Just ((minBound, maxBound), (maxBound, minBound)))] [] [] []
    check "bounded full artifact fields preserve exact minimum and maximum values" (fmap show (readMaybe (show boundaries) :: Maybe FullArtifact) == Just (show boundaries))
    let huge = 10 ^ (100 :: Int) + 7
        natural = artifact "2" "[1213156401,2,1,3,0,0,0,0,3,21,0,1,0,0,0,0,-1]" ("[SSConstant (SCLogical 2),SSConstant (SCBuiltin 2),SSConstant (SCNat " ++ show huge ++ ")]") "[]" "[]"
        presburger = SSPresburger (SFQuant True huge (SFModulo (SPVar huge) huge SPZero)) [huge] Nothing
    case deserializeFullBytecode natural of
        Left message -> ioError (userError message)
        Right program -> check "full artifact natural constants retain arbitrary precision" (fmap (show . storeSymbol) (IntMap.lookup 2 (fullSymbols program)) == Just (show (SSConstant (SCNat huge))))
    check "Presburger identifiers and moduli retain arbitrary precision" (fmap show (readMaybe (show presburger) :: Maybe StoredSymbol) == Just (show presburger) && isRight (restoreSymbol presburger))

    let omega = TC_Named "omega"
        alpha = TC_Named "alpha"
        unique hint = DC_Unique (Unique 17) (DispHint (Just hint))
        signature = Forall [] (TyCon (TCon omega Star))
        prepared = withRuntimeMetadata (Map.singleton omega Star) (Map.singleton (unique "original") signature) Map.empty base
        kinds = Map.fromList [(omega, Star), (alpha, Star)]
        types = Map.fromList [(DC_Named "new", Forall [] (TyCon (TCon alpha Star))), (unique "renamed", signature)]
        enriched = withRuntimeMetadata kinds types Map.empty prepared
        again = withRuntimeMetadata kinds types Map.empty enriched
        stored program = map (show . storeSymbol) (IntMap.elems (fullSymbols program))
        expected = stored prepared ++ map (show . SSConstant) [SCType "alpha", SCData "new"]
    check "runtime metadata preserves symbol IDs and appends only new identities in order" (stored enriched == expected)
    check "runtime metadata enrichment is idempotent" (stored again == expected && fullWords again == fullWords enriched)
    check "runtime metadata enrichment keeps role tables valid" (isRight (validateFullBytecode enriched))
    putStrLn "V1 full artifact regression: bounded integers, nested metadata, Read compatibility and arbitrary precision passed"
