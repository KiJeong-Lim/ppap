module Main where

import Control.Monad (unless)
import qualified Data.IntMap.Strict as IntMap
import qualified Data.Map.Strict as Map
import Hol.BETA.Constant (Constant (..))
import Hol.BETA.Header
import Hol.BETA.HOPU
import Hol.BETA.Runtime (primitiveBindingTypeOkay, scopeEscaping)
import Hol.BETA.TermNode
import System.Exit (exitFailure)
import Z.Utils (Unique (..))

assert :: String -> Bool -> IO ()
assert label okay = unless okay $ do
    putStrLn ("HOPU type regression failed: " ++ label)
    exitFailure

main :: IO ()
main = do
    assert "well-typed successor application was rejected"
        (typeOfTerm labeling [] goodValue == Just mkTyNat)
    assert "ill-typed successor application was assigned a result type"
        (typeOfTerm labeling [] badValue == Nothing)
    assert "primitive binding rejected a well-typed structured nat"
        (primitiveBindingTypeOkay labeling target goodValue)
    assert "primitive binding accepted s applied to a character"
        (not (primitiveBindingTypeOkay labeling target badValue))
    assert "type recovery ignored a suspension environment"
        (typeOfTerm suspensionLabeling [mkTyChr] explicitSuspension == Just mkTyNat)
    assert "scope checking ignored a rigid constant in a suspension environment"
        (scopeEscaping suspensionLabeling 0 target explicitSuspension == ([highConstant], []))
    putStrLn "HOPU application type regressions passed"
    where
        target = LV_Named "Target"
        goodValue = mkNApp (mkNCon DC_Succ) (mkNCon (DC_NatL 0))
        badValue = mkNApp (mkNCon DC_Succ) (mkNCon (DC_ChrL 'a'))
        labeling = Labeling
            { _ConLabel = IntMap.empty
            , _VarLabel = IntMap.empty
            , _ConTypes = IntMap.empty
            , _VarTypes = IntMap.empty
            , _NamedTypes = Map.singleton "Target" mkTyNat
            , _TyVarKeys = IntMap.empty
            , _TypeEnv = Map.singleton DC_Succ (Forall [] (mkTyNat `mkTyArrow` mkTyNat))
            }
        highConstant = DC (DC_Unique (Unique 7) noHint)
        explicitSuspension = mkSusp (mkNIdx 0) 1 0 [mkBinds (mkNCon highConstant) 0]
        suspensionLabeling = labeling
            { _ConLabel = IntMap.singleton 7 1
            , _ConTypes = IntMap.singleton 7 mkTyNat
            }
