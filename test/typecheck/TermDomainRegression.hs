module Main where

import Control.Exception (SomeException, evaluate, try)
import qualified Hol.ALPHA2.Constant as AlphaConstant
import qualified Hol.ALPHA2.Header as AlphaHeader
import qualified Hol.ALPHA2.TermNode as Alpha
import qualified Hol.BETA.Constant as BetaConstant
import qualified Hol.BETA.Header as BetaHeader
import qualified Hol.BETA.TermNode as Beta
import System.Exit (exitFailure)

assertUndefined :: String -> IO a -> IO ()
assertUndefined label action = do
    outcome <- try (action >> return ()) :: IO (Either SomeException ())
    case outcome of
        Left _ -> return ()
        Right () -> do
            putStrLn ("term-domain regression failed: " ++ label)
            exitFailure

assert :: String -> Bool -> IO ()
assert label okay
    | okay = return ()
    | otherwise = do
        putStrLn ("term-domain regression failed: " ++ label)
        exitFailure

main :: IO ()
main = do
    assertUndefined "ALPHA2 smart negative natural"
        (evaluate (Alpha.mkNCon (AlphaHeader.DC_NatL (-1))))
    assertUndefined "BETA smart negative natural"
        (evaluate (Beta.mkNCon (BetaHeader.DC_NatL (-1))))
    assertUndefined "ALPHA2 Constant overload cannot bypass the natural domain"
        (evaluate (Alpha.mkNCon (AlphaConstant.DC (AlphaHeader.DC_NatL (-1)))))
    assertUndefined "BETA Constant overload cannot bypass the natural domain"
        (evaluate (Beta.mkNCon (BetaConstant.DC (BetaHeader.DC_NatL (-1)))))
    assertUndefined "ALPHA2 forged negative natural normalization"
        (evaluate (Alpha.rewrite Alpha.NF (Alpha.NCon (AlphaConstant.DC (AlphaHeader.DC_NatL (-1))))))
    assertUndefined "BETA forged negative natural normalization"
        (evaluate (Beta.rewrite Beta.NF (Beta.NCon (BetaConstant.DC (BetaHeader.DC_NatL (-1))) Nothing)))
    let forgedAlphaNegative = Alpha.NCon (AlphaConstant.DC (AlphaHeader.DC_NatL (-1)))
        forgedBetaNegative = Beta.NCon (BetaConstant.DC (BetaHeader.DC_NatL (-1))) Nothing
    assertUndefined "ALPHA2 successor folded a forged negative natural into the domain"
        (evaluate (Alpha.mkNApp (Alpha.NCon (AlphaConstant.DC AlphaHeader.DC_Succ)) forgedAlphaNegative))
    assertUndefined "BETA successor folded a forged negative natural into the domain"
        (evaluate (Beta.mkNApp (Beta.NCon (BetaConstant.DC BetaHeader.DC_Succ) Nothing) forgedBetaNegative))
    assertUndefined "BETA located successor folded a forged negative natural into the domain"
        (evaluate (Beta.mkNAppLoc Nothing (Beta.NCon (BetaConstant.DC BetaHeader.DC_Succ) Nothing) forgedBetaNegative))

    let alphaX = Alpha.mkLVar (Alpha.LV_Named "X")
        betaX = Beta.mkLVar (Beta.LV_Named "X")
        forgedAlphaIndex = Alpha.NIdx (-1)
        forgedBetaIndex = Beta.NIdx (-1)
    assertUndefined "ALPHA2 application smart constructor accepted a bad function"
        (evaluate (Alpha.mkNApp forgedAlphaIndex alphaX))
    assertUndefined "ALPHA2 application smart constructor accepted a bad argument"
        (evaluate (Alpha.mkNApp alphaX forgedAlphaIndex))
    assertUndefined "BETA application smart constructor accepted a bad function"
        (evaluate (Beta.mkNApp forgedBetaIndex betaX))
    assertUndefined "BETA application smart constructor accepted a bad argument"
        (evaluate (Beta.mkNApp betaX forgedBetaIndex))
    assertUndefined "BETA located application smart constructor accepted a bad function"
        (evaluate (Beta.mkNAppLoc Nothing forgedBetaIndex betaX))
    assertUndefined "BETA located application smart constructor accepted a bad argument"
        (evaluate (Beta.mkNAppLoc Nothing betaX forgedBetaIndex))
    assertUndefined "ALPHA2 lambda smart constructor accepted a bad body"
        (evaluate (Alpha.mkNLam forgedAlphaIndex))
    assertUndefined "BETA lambda smart constructor accepted a bad body"
        (evaluate (Beta.mkNLam forgedBetaIndex))
    assertUndefined "BETA hinted lambda smart constructor accepted a bad body"
        (evaluate (Beta.mkNLamHint (Just "X") forgedBetaIndex))
    assertUndefined "BETA typed hinted lambda smart constructor accepted a bad body"
        (evaluate (Beta.mkNLamHintTy (Just "X") Beta.noLamType forgedBetaIndex))
    assertUndefined "BETA located lambda smart constructor accepted a bad body"
        (evaluate (Beta.mkNLamLoc Nothing (Just "X") Beta.noLamType forgedBetaIndex))
    assertUndefined "ALPHA2 empty application fold accepted a bad head"
        (evaluate (Alpha.foldlNApp forgedAlphaIndex []))
    assertUndefined "BETA empty application fold accepted a bad head"
        (evaluate (Beta.foldlNApp forgedBetaIndex []))
    assertUndefined "ALPHA2 zero-count nested lambda accepted a bad body"
        (evaluate (Alpha.makeNestedNLam 0 forgedAlphaIndex))
    assertUndefined "BETA zero-count nested lambda accepted a bad body"
        (evaluate (Beta.makeNestedNLam 0 forgedBetaIndex))
    assertUndefined "BETA empty hinted nested lambda accepted a bad body"
        (evaluate (Beta.makeNestedNLamH [] forgedBetaIndex))
    assertUndefined "ALPHA2 suspension-environment lens accepted a bad binding body"
        (evaluate (Alpha.lensForSuspEnv id [Alpha.Binds forgedAlphaIndex 0]))
    assertUndefined "BETA suspension-environment lens accepted a bad binding body"
        (evaluate (Beta.lensForSuspEnv id [Beta.Binds forgedBetaIndex 0]))
    assertUndefined "ALPHA2 negative suspension old level"
        (evaluate (Alpha.mkSusp alphaX (-1) 0 []))
    assertUndefined "BETA negative suspension old level"
        (evaluate (Beta.mkSusp betaX (-1) 0 []))
    assertUndefined "ALPHA2 negative suspension new level"
        (evaluate (Alpha.mkSusp alphaX 0 (-1) []))
    assertUndefined "BETA negative suspension new level"
        (evaluate (Beta.mkSusp betaX 0 (-1) []))
    assertUndefined "ALPHA2 suspension environment length mismatch"
        (evaluate (Alpha.mkSusp alphaX 1 0 []))
    assertUndefined "BETA suspension environment length mismatch"
        (evaluate (Beta.mkSusp betaX 1 0 []))
    assertUndefined "ALPHA2 suspension item above the new level"
        (evaluate (Alpha.mkSusp alphaX 1 0 [Alpha.Dummy 1]))
    assertUndefined "BETA suspension item above the new level"
        (evaluate (Beta.mkSusp betaX 1 0 [Beta.Dummy 1]))
    assertUndefined "ALPHA2 negative dummy level"
        (evaluate (Alpha.mkDummy (-1)))
    assertUndefined "BETA negative dummy level"
        (evaluate (Beta.mkDummy (-1)))
    assertUndefined "ALPHA2 forged malformed suspension at a semantic boundary"
        (evaluate (Alpha.rewrite Alpha.NF (Alpha.Susp alphaX 1 0 [])))
    assertUndefined "BETA forged malformed suspension at a semantic boundary"
        (evaluate (Beta.rewrite Beta.NF (Beta.Susp betaX 1 0 [])))
    assertUndefined "ALPHA2 trivial suspension smart constructor laundered a bad body"
        (evaluate (Alpha.mkSusp (Alpha.NIdx (-1)) 0 0 []))
    assertUndefined "BETA trivial suspension smart constructor laundered a bad body"
        (evaluate (Beta.mkSusp (Beta.NIdx (-1)) 0 0 []))
    assertUndefined "ALPHA2 suspension smart constructor accepted a bad environment body"
        (evaluate (Alpha.mkSusp alphaX 1 0 [Alpha.Binds (Alpha.NIdx (-1)) 0]))
    assertUndefined "BETA suspension smart constructor accepted a bad environment body"
        (evaluate (Beta.mkSusp betaX 1 0 [Beta.Binds (Beta.NIdx (-1)) 0]))
    assertUndefined "ALPHA2 binding smart constructor accepted a bad body"
        (evaluate (Alpha.mkBinds (Alpha.NIdx (-1)) 0))
    assertUndefined "BETA binding smart constructor accepted a bad body"
        (evaluate (Beta.mkBinds (Beta.NIdx (-1)) 0))

    let alphaBound = Alpha.mkNCon (AlphaHeader.DC_NatL 7)
        betaBound = Beta.mkNCon (BetaHeader.DC_NatL 7)
        alphaValid = Alpha.mkSusp (Alpha.NIdx 0) 1 0 [Alpha.Binds alphaBound 0]
        betaValid = Beta.mkSusp (Beta.NIdx 0) 1 0 [Beta.Binds betaBound 0]
    assert "ALPHA2 rejected a well-formed explicit suspension"
        (Alpha.rewrite Alpha.NF alphaValid == alphaBound)
    assert "BETA rejected a well-formed explicit suspension"
        (Beta.rewrite Beta.NF betaValid == betaBound)

    let expectedShows = ["=<", "<", ">=", ">", "+", "-", "*", "/", "_"]
        alphaShows = map show
            [ AlphaHeader.DC_le, AlphaHeader.DC_lt, AlphaHeader.DC_ge
            , AlphaHeader.DC_gt, AlphaHeader.DC_plus, AlphaHeader.DC_minus
            , AlphaHeader.DC_mul, AlphaHeader.DC_div, AlphaHeader.DC_wc
            ]
        betaShows = map show
            [ BetaHeader.DC_le, BetaHeader.DC_lt, BetaHeader.DC_ge
            , BetaHeader.DC_gt, BetaHeader.DC_plus, BetaHeader.DC_minus
            , BetaHeader.DC_mul, BetaHeader.DC_div, BetaHeader.DC_wc
            ]
    assert "ALPHA2 DataConstructor Show is not exhaustive" (alphaShows == expectedShows)
    assert "BETA DataConstructor Show is not exhaustive" (betaShows == expectedShows)
    putStrLn "term-domain regressions passed"
