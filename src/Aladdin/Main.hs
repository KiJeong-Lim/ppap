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

runAladdin :: UniqueGenT IO ()
runAladdin = do
    let eq_facts = [mkNApp (mkNCon LO_ty_pi) (mkNAbs (mkNApp (mkNCon LO_pi) (mkNAbs (mkNApp (mkNApp (mkNApp (mkNCon DC_Eq) (mkNIdx 2)) (mkNIdx 1)) (mkNIdx 1)))))]
    dir <- lift $ do
        putStr "Aladdin<<< "
        hFlush stdout
        getLine
    if dir == ""
        then do
            lift $ putStrLn "No module loaded"
            runREPL (Program{ _KindDecls = theInitialKindEnv, _TypeDecls = theInitialTypeEnv, _FactDecls = eq_facts })
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
                            module1 <- desugarProgram theInitialKindEnv theInitialTypeEnv program1
                            facts2 <- sequence [ checkType (_TypeDecls module1) fact mkTyO | fact <- _FactDecls module1 ]
                            facts3 <- sequence [ convertProgram used_mtvs assumptions fact | (fact, (used_mtvs, assumptions)) <- facts2 ]
                            return (Program { _KindDecls = _KindDecls module1, _TypeDecls = _TypeDecls module1, _FactDecls = eq_facts ++ facts3 })
                        case result of
                            Left err_msg -> do
                                lift $ putStrLn err_msg
                                runAladdin
                            Right program2 -> do
                                lift $ putStrLn ("Loaded: " ++ dir)
                                runREPL program2

main :: IO ()
main = do
    runUniqueGenT runAladdin
    return ()
