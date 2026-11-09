module Hol.ALPHA1.Main (main, theInitialFactDecls, theInitialKindDecls, theInitialTypeDecls) where

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
import Control.Monad.Trans.Class
import Control.Monad.Trans.Except
import qualified Data.List as List
import qualified Data.Map.Strict as Map
import System.Directory (canonicalizePath, makeRelativeToCurrentDirectory)
import System.FilePath (dropExtension, isRelative, splitDirectories, takeBaseName)
import System.IO.Error (isEOFError)
import Z.System.File (readFileNow)
import Z.System.Path
import Z.System.Shelly

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
theDefaultModuleName = "hol"

runAlpha1 :: UniqueGenT IO ()
runAlpha1 = do
    file_dir <- lift $ shelly "hol =<< "
    case matchFileDirWithExtension file_dir of
        ("", "") -> do
            lift $ shelly (theDefaultModuleName ++ "> Ok, no module loaded.")
            runREPL (Program { _KindDecls = theInitialKindDecls, _TypeDecls = theInitialTypeDecls, _FactDecls = theInitialFactDecls, moduleName = theDefaultModuleName })
        (file_name, extension)
            | extension `elem` ["", ".hol"] -> loadModule file_name
            | otherwise -> do
                lift $ putStrLn ("*** loading-error: `" ++ extension ++ "\' is not the extension of a hol module; expected `.hol\'.")
                runAlpha1
    where
        loadModule :: String -> UniqueGenT IO ()
        loadModule file_name = do
            let my_file_dir = file_name ++ ".hol"
            maybe_src <- lift $ readFileNow my_file_dir
            case maybe_src of
                Nothing -> do
                    lift $ putStrLn ("*** loading-error: couldn't read the file `" ++ my_file_dir ++ "\'.")
                    runAlpha1
                Just src -> do
                    file_abs_dir <- lift (canonicalizePath my_file_dir)
                    myModuleName <- lift $ moduleNameOf file_abs_dir
                    lift $ shelly (theDefaultModuleName ++ "> Compiling " ++ myModuleName ++ " ( " ++ file_abs_dir ++ ", interpreted )")
                    case runAnalyzer src of
                        Left err_msg -> do
                            lift $ putStrLn err_msg
                            runAlpha1
                        Right (Left _) -> do
                            lift $ putStrLn "*** parsing-error: it is not a program."
                            runAlpha1
                        Right (Right program1) -> do
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
        moduleNameOf :: FilePath -> IO String
        moduleNameOf path = do
            relative_path <- makeRelativeToCurrentDirectory path
            let components = splitDirectories (dropExtension relative_path)
            return (if isRelative relative_path && ".." `notElem` components then List.intercalate "." components else takeBaseName path)

main :: IO ()
main = runUniqueGenT runAlpha1 `catch` endOfInput where
    endOfInput :: IOException -> IO ()
    endOfInput err
        | isEOFError err = return ()
        | otherwise = ioError err
