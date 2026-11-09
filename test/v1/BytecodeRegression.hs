module Main where

import Control.Exception (IOException, try)
import Control.Monad
import Data.Either (isLeft)
import Data.Int
import qualified Data.IntMap.Strict as IntMap
import qualified Data.Map.Strict as Map
import Data.Maybe (isNothing)
import Hol.BETA.Constant
import Hol.BETA.Header
import Hol.BETA.HOPU
import qualified Hol.BETA.Main as BETA
import Hol.BETA.TermNode
import Hol.V1.Bytecode
import Hol.V1.Compiler
import Hol.V1.Runtime (decodeAnswer, inferAnswerTypes)
import qualified X.Machine as Native
import System.Timeout (timeout)
import Z.Utils

check :: String -> Bool -> IO ()
check label condition = unless condition (ioError (userError label))

right :: Either String a -> IO a
right = either (ioError . userError) return

answers :: CompiledProgram -> IO [[Int64]]
answers program = Native.withMachine (bytecodeWords program) go where
    go machine = do
        answer <- Native.nextAnswer machine >>= right
        case answer of
            Nothing -> return []
            Just value -> (value :) <$> go machine

change :: Int -> a -> [a] -> [a]
change index value values = take index values ++ [value] ++ drop (index + 1) values

main :: IO ()
main = do
    let name = mkNCon . DC_Named
        predicate arg = mkNApp (name "p") arg
        x = LV_Named "X"
        y = LV_Named "Y"
    program <- right (compileProgram [predicate (name "red"), predicate (name "blue")] (predicate (mkLVar x)))
    encoded <- answers program
    decoded <- execUniqueT (mapM (decodeAnswer program) encoded)
    bindings <- mapM right decoded
    check "compiled calls must enumerate clauses in source order" (map unVarBinding bindings == [Map.singleton x (name "red"), Map.singleton x (name "blue")])
    let p = LV_Named "P"
        functionType = foldlNApp (mkNCon TC_Arrow) [mkNCon (TC_Named "color"), mkNCon (TC_Named "o")]
        bindPredicate = foldlNApp (mkNCon DC_eq) [functionType, mkLVar p, name "p"]
        dynamicCall = mkNApp (mkLVar p) (mkLVar x)
        conjunction lhs rhs = foldlNApp (mkNCon LO_and) [lhs, rhs]
        predicateFacts = [predicate (name "red"), predicate (name "blue")]
        standardFacts = BETA.theInitialFactDecls ++ predicateFacts
    specialized <- right (compileProgram standardFacts (conjunction bindPredicate dynamicCall))
    specializedWords <- answers specialized
    specializedBindings <- execUniqueT (mapM (decodeAnswer specialized) specializedWords) >>= mapM right
    check "closed predicate aliases retain observable bindings and clause order" (map unVarBinding specializedBindings == [Map.fromList [(p, name "p"), (x, name "red")], Map.fromList [(p, name "p"), (x, name "blue")]])
    check "later equalities cannot justify an earlier dynamic call" (isLeft (compileProgram standardFacts (conjunction dynamicCall bindPredicate)))
    check "custom equality prevents predicate alias specialization" (isLeft (compileProgram (standardFacts ++ [bindPredicate]) (conjunction bindPredicate dynamicCall)))
    artifact <- right (serializeBytecode program)
    restored <- right (deserializeBytecode artifact)
    replay <- answers restored
    check "artifact execution must preserve exact native answers" (replay == encoded)
    check "artifact metadata roundtrip" (bytecodeVariables restored == [x] && bytecodeConstants restored == bytecodeConstants program)
    check "artifact trailing junk must be rejected" (isLeft (deserializeBytecode (artifact ++ "junk")))
    check "artifact wrong version must be rejected" (isLeft (deserializeBytecode (show (BytecodeArtifact 2 [] [] [] 0))))
    let artifactWith version table = "BytecodeArtifact " ++ version ++ " " ++ table ++ " [] [] 0"
        limits = [minBound, maxBound, 0, -1] :: [Int64]
        limitTables =
            [ show limits
            , "[ -9223372036854775808, 9223372036854775807, 0, -1 ]"
            , "[-0x8000000000000000,0x7fffffffffffffff,0,-1]"
            ]
    forM_ limitTables $ \table -> case readBytecodeArtifact (artifactWith "1" table) of
        Just (BytecodeArtifact 1 words [] [] 0) -> check "artifact parsing must preserve exact Int64 boundaries" (words == limits)
        _ -> ioError (userError "artifact parsing rejected valid Int64 boundaries")
    compatible <- right (deserializeBytecode (" (\n" ++ artifact ++ ") \n"))
    check "artifact loading must preserve noncanonical Read syntax" (bytecodeWords compatible == bytecodeWords program)
    forM_ ["9223372036854775808", "-9223372036854775809", "18446744073709551616", "0x10000000000000000"] $ \overflow -> do
        check "artifact word overflow must be rejected" (isNothing (readBytecodeArtifact (artifactWith "1" ("[" ++ overflow ++ "]"))))
        check "artifact fallback word overflow must be rejected" (isNothing (readBytecodeArtifact (artifactWith "1" ("[ " ++ overflow ++ " ]"))))
        check "artifact version overflow must be rejected" (isNothing (readBytecodeArtifact (artifactWith overflow "[]")))
    forM_ ["-", "1,", "1,,2", "1 2", "0x", "1e2"] $ \table ->
        check "malformed artifact words must be rejected" (isNothing (readBytecodeArtifact (artifactWith "1" ("[" ++ table ++ "]"))))
    check "artifact missing closing bracket must be rejected" (isNothing (readBytecodeArtifact (artifactWith "1" "[0")))
    check "metadata mismatch must be rejected" (isLeft (validateBytecode (program { bytecodeQuerySlots = 0 })))
    check "negative natural metadata must be rejected" (isLeft (validateBytecode (program { bytecodeConstants = IntMap.insert 0 (DC (DC_NatL (-1))) (bytecodeConstants program) })))
    check "negative variable identity must be rejected" (isLeft (validateBytecode (program { bytecodeVariables = [LV_Unique (Unique (-1)) noHint] })))

    let ret = [bytecodeMagic, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]
        badSlot = [bytecodeMagic, 1, 1, 2, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0]
        malformed =
            [ []
            , change 0 0 ret
            , change 1 2 ret
            , change 2 maxBound ret
            , change 6 1 ret
            , change 8 17 ret
            , init ret
            , ret ++ [0]
            , badSlot
            , [bytecodeMagic, 1, 1, 1, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0]
            ]
        wrappedMagic = toInteger bytecodeMagic + 2 ^ (64 :: Int)
    check "overflow cannot wrap into a valid bytecode header" (isLeft (deserializeBytecode (artifactWith "1" (show (wrappedMagic : map toInteger (tail ret))))))
    forM_ (zip [0 :: Int ..] malformed) $ \(index, code) -> do
        result <- Native.withMachine code Native.nextAnswer
        check ("invalid wordcode must report an error: " ++ show index) (isLeft result)
    check "artifact validation checks slots before entering C" (isLeft (validateBytecode (CompiledProgram badSlot IntMap.empty [] 0)))
    case bytecodeWords program of
        _ : _ : termCount : instructionCount : _ : _ : _ : symbolCount : _ -> do
            let offset = 8 + fromIntegral termCount * 3 + fromIntegral instructionCount * 4
                oldSymbol = bytecodeWords program !! offset
                wrongHead = change offset ((oldSymbol + 1) `mod` symbolCount) (bytecodeWords program)
            check "artifact validation rejects a mismatched clause head" (isLeft (validateBytecode (program { bytecodeWords = wrongHead })))
        _ -> ioError (userError "compiler produced no bytecode header")
    Native.withMachine ret $ \machine -> do
        first <- Native.nextAnswer machine
        second <- Native.nextAnswer machine
        third <- Native.nextAnswer machine
        check "RETURN must yield once, then remain exhausted" (first == Right (Just []) && second == Right Nothing && third == Right Nothing)
    machine <- Native.createMachine ret
    Native.closeMachine machine
    Native.closeMachine machine
    closed <- Native.nextAnswer machine
    check "a closed machine must reject execution" (isLeft closed)
    escaped <- try (Native.withMachine ret (const (ioError (userError "callback failed")))) :: IO (Either IOException ())
    check "bracket propagates callback exceptions" (isLeft escaped)
    let infinite = [bytecodeMagic, 1, 0, 1, 0, 0, 0, 0, 5, 0, 0, 0]
    Native.withMachine infinite $ \looping -> do
        stopped <- timeout 100000 (Native.nextAnswer looping)
        check "native loops must remain interruptible" (stopped == Nothing)
        Native.closeMachine looping
        after <- Native.nextAnswer looping
        check "an interrupted machine can be closed" (isLeft after)

    let alias = CompiledProgram [bytecodeMagic, 1, 2, 2, 0, 2, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 3, 0, 1, 0] IntMap.empty [x, y] 2
    aliasWords <- answers alias
    aliasBinding <- execUniqueT (decodeAnswer alias (concat aliasWords)) >>= right
    let named = unVarBinding aliasBinding
    check "unification preserves an unbound alias shared by both query variables" (Map.member x named && Map.lookup x named == Map.lookup y named)
    untouched <- execUniqueT (decodeAnswer alias [0, 0, 0, 1]) >>= right
    check "unbound original query slots are not reported as substitutions" (Map.null (unVarBinding untouched))
    forM_ [[], [0], [0, -1], [1, 999], [3], [2, 0, 0], [0, 0, 0, 1, 0]] $ \words -> do
        result <- execUniqueT (decodeAnswer alias words)
        check "malformed native answer must be rejected" (isLeft result)
    let residual = LV_Unique (Unique 10) noHint
        tree = TyCon (TCon (TC_Named "tree") Star)
        kinds = Map.insert (TC_Named "tree") Star BETA.theInitialKindDecls
        types = Map.insert (DC_Named "branch") (Forall [] (mkTyArrow tree tree)) BETA.theInitialTypeDecls
        infer queryTypes substitutions = inferAnswerTypes kinds types (Map.fromList queryTypes) (VarBinding (Map.fromList substitutions))
        branch = mkNApp (name "branch") (mkLVar residual)
        listType = mkNCon (TC_Named "tree")
        listValue = mkNApp (mkNApp (mkNApp (mkNCon DC_Cons) listType) (mkLVar residual)) (mkNApp (mkNCon DC_Nil) listType)
    check "answer callback recovers residual constructor variable types" (Map.lookup residual (infer [(x, tree)] [(x, branch)]) == Just tree)
    check "answer callback instantiates polymorphic list type arguments" (Map.lookup residual (infer [(x, mkTyList tree)] [(x, listValue)]) == Just tree)
    check "answer callback does not guess unknown constructor argument types" (Map.notMember residual (infer [(x, tree)] [(x, mkNApp (name "unknown") (mkLVar residual))]))
    check "answer callback discards conflicting type evidence" (Map.notMember residual (infer [(x, tree), (y, mkTyNat)] [(x, mkLVar residual), (y, mkLVar residual)]))
    putStrLn "V1 bytecode regression: compiler, artifact, validation, FFI lifetime and answer sharing passed"
