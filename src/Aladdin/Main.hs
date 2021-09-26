module Aladdin.Main where

import Aladdin.Back.BackEnd
import Aladdin.Back.Base.Constant
import Aladdin.Back.Base.TermNode
import Aladdin.Back.Base.TermNode.Show
import Aladdin.Back.Base.TermNode.Util
import Aladdin.Back.Base.VarBinding
import Aladdin.Back.Converter.Main
import Aladdin.Back.HOPU.Util
import Aladdin.Back.Runtime.Main
import Aladdin.Back.Runtime.Util
import Aladdin.Front.Analyzer.Main
import Aladdin.Front.Desugarer.Main
import Aladdin.Front.Header
import Aladdin.Front.TypeChecker.Main
import Control.Monad
import Control.Monad.Trans.Class
import Control.Monad.Trans.Except
import Control.Monad.Trans.State.Strict
import Data.IORef
import qualified Data.List as List
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import System.Exit
import System.IO
import Z.System.Path
import Z.System.Pretty
import Z.Utils

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
    , (DC_LO LO_sigma, Forall ["a"] ((TyVar 0 `mkTyArrow` mkTyO) `mkTyArrow` mkTyO))
    , (DC_LO LO_pi, Forall ["a"] ((TyVar 0 `mkTyArrow` mkTyO) `mkTyArrow` mkTyO))
    , (DC_LO LO_cut, Forall [] (mkTyO))
    , (DC_LO LO_true, Forall [] (mkTyO))
    , (DC_LO LO_fail, Forall [] (mkTyO))
    , (DC_Nil, Forall ["a"] (mkTyList (TyVar 0)))
    , (DC_Cons, Forall ["a"] (TyVar 0 `mkTyArrow` (mkTyList (TyVar 0) `mkTyArrow` mkTyList (TyVar 0))))
    , (DC_Succ, Forall [] (mkTyNat `mkTyArrow` mkTyNat))
    , (DC_Eq, Forall ["a"] (TyVar 0 `mkTyArrow` (TyVar 0 `mkTyArrow` mkTyO)))
    ]

theInitialFactDecls :: [TermNode]
theInitialFactDecls = [eqFact] where
    eqFact :: TermNode
    eqFact = mkNApp (mkNCon LO_ty_pi) (mkNAbs (mkNApp (mkNCon LO_pi) (mkNAbs (mkNApp (mkNApp (mkNApp (mkNCon DC_Eq) (mkNIdx 2)) (mkNIdx 1)) (mkNIdx 1)))))

theDefaultModuleName :: String
theDefaultModuleName = "aladdin"

runAladdin :: UniqueGenT IO ()
runAladdin = do
    consistency_ptr <- lift $ newIORef ""
    file_dir <- lift $ shelly "Aladdin =<< "
    maybe_file_name <- case matchFileDirWithExtension file_dir of
        ("", "") -> return Nothing
        (file_name, ".aladdin") -> return (Just file_name)
        (file_name, "") -> return (Just file_name)
        (file_name, '.' : wrong_extension) -> do
            lift $ writeIORef consistency_ptr (theDefaultModuleName ++ "> " ++ shows wrong_extension " is a non-executable file extension.")
            return Nothing
    consistency <- lift $ readIORef consistency_ptr
    case consistency of
        "" -> case maybe_file_name of
            Nothing -> do
                lift $ shelly (theDefaultModuleName ++ "> Ok, no module loaded.")
                runREPL (Program{ _KindDecls = theInitialKindDecls, _TypeDecls = theInitialTypeDecls, _FactDecls = theInitialFactDecls, moduleName = theDefaultModuleName })
            Just file_name -> do
                let my_file_dir = file_name ++ ".aladdin"
                src <- lift $ readFile my_file_dir
                file_abs_dir <- fmap (maybe my_file_dir id) (lift $ makePathAbsolutely my_file_dir)
                lift $ shelly (theDefaultModuleName ++ "> Compiling " ++ file_name ++ "  ( " ++ file_abs_dir ++ " )")
                case runAnalyzer src of
                    Left err_msg -> do
                        lift $ putStrLn err_msg
                        runAladdin
                    Right output -> case output of
                        Left query1 -> do
                            lift $ putStrLn "*** parsing-error: it is not a program."
                            runAladdin
                        Right program1 -> do
                            result <- runExceptT $ do
                                module1 <- desugarProgram theInitialKindDecls theInitialTypeDecls theDefaultModuleName program1
                                facts2 <- sequence [ checkType (_TypeDecls module1) fact mkTyO | fact <- _FactDecls module1 ]
                                facts3 <- sequence [ convertProgram used_mtvs assumptions fact | (fact, (used_mtvs, assumptions)) <- facts2 ]
                                return (Program { _KindDecls = _KindDecls module1, _TypeDecls = _TypeDecls module1, _FactDecls = theInitialFactDecls ++ facts3, moduleName = file_name })
                            case result of
                                Left err_msg -> do
                                    lift $ putStrLn err_msg
                                    runAladdin
                                Right program2 -> do
                                    lift $ shelly (file_name ++ "> Ok, one module loaded.")
                                    runREPL program2
        inconsistent_proof -> do
            lift $ shelly inconsistent_proof
            lift $ shelly ("Aladdin >>= quit")
            return ()

main :: IO ()
main = do
    runUniqueGenT runAladdin
    return ()
