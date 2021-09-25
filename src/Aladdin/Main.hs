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
import qualified Data.List as List
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import System.Exit
import System.IO

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
theInitialFactDecls =
    [ mkNApp (mkNCon LO_ty_pi) (mkNAbs (mkNApp (mkNCon LO_pi) (mkNAbs (mkNApp (mkNApp (mkNApp (mkNCon DC_Eq) (mkNIdx 2)) (mkNIdx 1)) (mkNIdx 1)))))
    ]

runAladdin :: UniqueGenT IO ()
runAladdin = do
    dir <- lift $ do
        putStr "Aladdin<<< "
        hFlush stdout
        getLine
    if dir == ""
        then do
            lift $ putStrLn "Aladdin> Print (No module loaded)."
            runREPL (Program{ _KindDecls = theInitialKindDecls, _TypeDecls = theInitialTypeDecls, _FactDecls = theInitialFactDecls })
        else do
            src <- lift $ readFile dir
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
                            module1 <- desugarProgram theInitialKindDecls theInitialTypeDecls program1
                            facts2 <- sequence [ checkType (_TypeDecls module1) fact mkTyO | fact <- _FactDecls module1 ]
                            facts3 <- sequence [ convertProgram used_mtvs assumptions fact | (fact, (used_mtvs, assumptions)) <- facts2 ]
                            return (Program { _KindDecls = _KindDecls module1, _TypeDecls = _TypeDecls module1, _FactDecls = theInitialFactDecls ++ facts3 })
                        case result of
                            Left err_msg -> do
                                lift $ putStrLn err_msg
                                runAladdin
                            Right program2 -> do
                                lift $ putStrLn ("Aladdin> Print (One module loaded: " ++ dir ++ ").")
                                runREPL program2

main :: IO ()
main = do
    runUniqueGenT runAladdin
    return ()
