module Hol.ALPHA1.Main (main) where

import Hol.ALPHA1.Back.BackEnd
import Hol.ALPHA1.Back.Base.Constant
import Hol.ALPHA1.Back.Base.TermNode
import Hol.ALPHA1.Back.Base.TermNode.Show
import Hol.ALPHA1.Back.Base.TermNode.Util
import Hol.ALPHA1.Back.Base.VarBinding
import Hol.ALPHA1.Back.Converter.Main
import Hol.ALPHA1.Back.HOPU.Util
import Hol.ALPHA1.Back.Runtime.Main
import Hol.ALPHA1.Back.Runtime.Util
import Hol.ALPHA1.Front.Analyzer.Main
import Hol.ALPHA1.Front.Desugarer.Main
import Hol.ALPHA1.Front.Header
import Hol.ALPHA1.Front.TypeChecker.Main
import Control.Exception (IOException, catch)
import Control.Monad
import Control.Monad.Trans.Class
import Control.Monad.Trans.Except
import Control.Monad.Trans.State.Strict
import Data.IORef
import qualified Data.List as List
import qualified Data.Map.Strict as Map
import Data.Maybe
import qualified Data.Set as Set
import System.Exit
import System.IO
import System.IO.Error (isEOFError)
import Z.System.File (readFileNow)
import Z.System.Path
import Z.System.Shelly
import Z.Utils hiding (ErrMsg, Unique, unUnique, UniqueT, runUniqueT, HasAnnot, getAnnot, setAnnot)

theInitialKindDecls :: KindEnv
theInitialKindDecls = Map.fromList
    [ (TC_Arrow, read "* -> * -> *")
    , (TC_Named "list", read "* -> *")
    , (TC_Named "o", read "*")
    , (TC_Named "char", read "*")
    , (TC_Named "nat", read "*")
    , (TC_Named "string", read "*")
    ]

theInitialTypeDecls :: TypeEnv
theInitialTypeDecls = Map.fromList
    [ (DC_LO LO_if, Forall [] (mkTyO `mkTyArrow` (mkTyO `mkTyArrow` mkTyO)))
    , (DC_LO LO_and, Forall [] (mkTyO `mkTyArrow` (mkTyO `mkTyArrow` mkTyO)))
    , (DC_LO LO_or, Forall [] (mkTyO `mkTyArrow` (mkTyO `mkTyArrow` mkTyO)))
    , (DC_LO LO_imply, Forall [] (mkTyO `mkTyArrow` (mkTyO `mkTyArrow` mkTyO)))
    , (DC_LO LO_sigma, Forall ["A"] ((TyVar 0 `mkTyArrow` mkTyO) `mkTyArrow` mkTyO))
    , (DC_LO LO_pi, Forall ["A"] ((TyVar 0 `mkTyArrow` mkTyO) `mkTyArrow` mkTyO))
    , (DC_LO LO_cut, Forall [] (mkTyO))
    , (DC_LO LO_true, Forall [] (mkTyO))
    , (DC_LO LO_fail, Forall [] (mkTyO))
    , (DC_LO LO_debug, Forall [] (mkTyList mkTyChr `mkTyArrow` mkTyO))
    , (DC_Nil, Forall ["A"] (mkTyList (TyVar 0)))
    , (DC_Cons, Forall ["A"] (TyVar 0 `mkTyArrow` (mkTyList (TyVar 0) `mkTyArrow` mkTyList (TyVar 0))))
    , (DC_Succ, Forall [] (mkTyNat `mkTyArrow` mkTyNat))
    , (DC_Eq, Forall ["A"] (TyVar 0 `mkTyArrow` (TyVar 0 `mkTyArrow` mkTyO)))
    , (DC_LO (LO_Arith AP_Is), Forall [] (mkTyNat `mkTyArrow` (mkTyNat `mkTyArrow` mkTyO)))
    , (DC_LO (LO_Arith AP_Eq), Forall [] (mkTyNat `mkTyArrow` (mkTyNat `mkTyArrow` mkTyO)))
    , (DC_LO (LO_Arith AP_Ne), Forall [] (mkTyNat `mkTyArrow` (mkTyNat `mkTyArrow` mkTyO)))
    , (DC_LO (LO_Arith AP_Lt), Forall [] (mkTyNat `mkTyArrow` (mkTyNat `mkTyArrow` mkTyO)))
    , (DC_LO (LO_Arith AP_Le), Forall [] (mkTyNat `mkTyArrow` (mkTyNat `mkTyArrow` mkTyO)))
    , (DC_LO (LO_Arith AP_Gt), Forall [] (mkTyNat `mkTyArrow` (mkTyNat `mkTyArrow` mkTyO)))
    , (DC_LO (LO_Arith AP_Ge), Forall [] (mkTyNat `mkTyArrow` (mkTyNat `mkTyArrow` mkTyO)))
    , (DC_Arith AO_Add, Forall [] (mkTyNat `mkTyArrow` (mkTyNat `mkTyArrow` mkTyNat)))
    , (DC_Arith AO_Subtract, Forall [] (mkTyNat `mkTyArrow` (mkTyNat `mkTyArrow` mkTyNat)))
    , (DC_Arith AO_Multiply, Forall [] (mkTyNat `mkTyArrow` (mkTyNat `mkTyArrow` mkTyNat)))
    , (DC_Arith AO_Divide, Forall [] (mkTyNat `mkTyArrow` (mkTyNat `mkTyArrow` mkTyNat)))
    , (DC_Arith AO_Quotient, Forall [] (mkTyNat `mkTyArrow` (mkTyNat `mkTyArrow` mkTyNat)))
    , (DC_Arith AO_Div, Forall [] (mkTyNat `mkTyArrow` (mkTyNat `mkTyArrow` mkTyNat)))
    , (DC_Arith AO_Mod, Forall [] (mkTyNat `mkTyArrow` (mkTyNat `mkTyArrow` mkTyNat)))
    , (DC_Arith AO_Rem, Forall [] (mkTyNat `mkTyArrow` (mkTyNat `mkTyArrow` mkTyNat)))
    , (DC_Arith AO_Positive, Forall [] (mkTyNat `mkTyArrow` mkTyNat))
    , (DC_Arith AO_Negate, Forall [] (mkTyNat `mkTyArrow` mkTyNat))
    ]

theInitialFactDecls :: [TermNode]
theInitialFactDecls = [eqFact] where
    eqFact :: TermNode
    eqFact = mkNApp (mkNCon LO_ty_pi) (mkNAbs (mkNApp (mkNCon LO_pi) (mkNAbs (mkNApp (mkNApp (mkNApp (mkNCon DC_Eq) (mkNIdx 2)) (mkNIdx 1)) (mkNIdx 1)))))

theDefaultModuleName :: String
theDefaultModuleName = "Aladdin"

runAlpha1 :: UniqueGenT IO ()
runAlpha1 = do
    consistency_ptr <- lift $ newIORef ""
    file_dir <- lift $ shelly "Aladdin =<< "
    maybe_file_name <- case matchFileDirWithExtension file_dir of
        ("", "") -> return Nothing
        (file_name, ".hol") -> return (Just file_name)
        (file_name, "") -> return (Just file_name)
        (file_name, '.' : wrong_extension) -> do
            lift $ writeIORef consistency_ptr (theDefaultModuleName ++ "> " ++ shows wrong_extension " is a non-executable file extension.")
            return Nothing
    consistency <- lift $ readIORef consistency_ptr
    case consistency of
        "" -> case maybe_file_name of
            Nothing -> do
                lift $ shelly (theDefaultModuleName ++ "> Ok, no module loaded.")
                runREPL (Program { _KindDecls = theInitialKindDecls, _TypeDecls = theInitialTypeDecls, _FactDecls = theInitialFactDecls, moduleName = theDefaultModuleName })
            Just file_name -> do
                let my_file_dir = file_name ++ ".hol"
                    myModuleName = modifySep '/' (const ".") id file_name
                maybe_src <- lift $ readFileNow my_file_dir
                case maybe_src of
                    Nothing -> do
                        lift $ putStrLn ("*** loading-error: couldn't read the file `" ++ my_file_dir ++ "'.")
                        runAlpha1
                    Just src -> do
                        file_abs_dir <- fmap (fromMaybe my_file_dir) (lift $ makePathAbsolutely my_file_dir)
                        lift $ shelly (theDefaultModuleName ++ "> Compiling " ++ myModuleName ++ " ( " ++ file_abs_dir ++ ", interpreted )")
                        case runAnalyzer src of
                            Left err_msg -> do
                                lift $ putStrLn err_msg
                                runAlpha1
                            Right output -> case output of
                                Left query1 -> do
                                    lift $ putStrLn "*** parsing-error: it is not a program."
                                    runAlpha1
                                Right program1 -> do
                                    result <- runExceptT $ do
                                        module1 <- desugarProgram theInitialKindDecls theInitialTypeDecls theDefaultModuleName program1
                                        facts2 <- sequence [ checkType (_TypeDecls module1) fact mkTyO | fact <- _FactDecls module1 ]
                                        facts3 <- sequence [ convertProgram used_mtvs assumptions fact | (fact, (used_mtvs, assumptions)) <- facts2 ]
                                        return (Program { _KindDecls = _KindDecls module1, _TypeDecls = _TypeDecls module1, _FactDecls = theInitialFactDecls ++ facts3, moduleName = myModuleName })
                                    case result of
                                        Left err_msg -> do
                                            lift $ putStrLn err_msg
                                            runAlpha1
                                        Right program2 -> do
                                            lift $ shelly (myModuleName ++ "> Ok, one module loaded.")
                                            runREPL program2
        inconsistent_proof -> do
            lift $ shelly inconsistent_proof
            lift $ shelly ("Aladdin >>= quit")
            return ()

main :: IO ()
main = runUniqueGenT runAlpha1 `catch` endOfInput where
    endOfInput :: IOException -> IO ()
    endOfInput err
        | isEOFError err = return ()
        | otherwise = ioError err
