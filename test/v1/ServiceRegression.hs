module Main where

import Control.Monad
import Control.Monad.Trans.Except
import Data.IORef
import qualified Data.IntMap.Strict as IntMap
import qualified Data.Map.Strict as Map
import Hol.BETA.Constant
import Hol.BETA.Debugger
import Hol.BETA.Header
import Hol.BETA.HOPU
import qualified Hol.BETA.Main as BETA
import qualified Hol.BETA.Notation as Notation
import Hol.BETA.Runtime
import Hol.BETA.TermNode
import Hol.V1.Services
import Z.Utils

check :: String -> Bool -> IO ()
check label okay = unless okay (ioError (userError label))

main :: IO ()
main = do
    debugging <- newIORef False
    pending <- newIORef mempty
    verbose <- newIORef False
    stack <- newIORef []
    cache <- newIORef initialCache
    output <- newIORef []
    input <- newIORef (Just (mkNCon (DC_NatL 8)))
    let x = LV_Named "X"
        y = LV_Named "Y"
        variable = mkLVar
        nat = mkNCon . DC_NatL
        binary con a b = mkNApp (mkNApp (mkNCon con) a) b
        labels = Labeling IntMap.empty IntMap.empty IntMap.empty IntMap.empty (Map.fromList [("X", mkTyNat), ("Y", mkTyNat)]) IntMap.empty BETA.theInitialTypeDecls
        context = Context mempty labels [] (Unique 0) debugging
        env = RuntimeEnv
            { _PutStr = \_ _ _ -> return ()
            , _Answer = \_ -> return False
            , _PrintPrimitive = \_ term -> modifyIORef' output (++ [term])
            , _ReadPrimitive = \_ _ -> readIORef input
            , _TypeInfo = Map.fromList [(x, mkTyNat), (y, mkTyNat)]
            , _PendingSubst = pending
            , _ProgramKindEnv = BETA.theInitialKindDecls
            , _ProgramTypeEnv = BETA.theInitialTypeDecls
            , _VerboseTyping = verbose
            , _StackRef = stack
            , _NameCacheRef = cache
            , _DebuggingRef = debugging
            , _NotationDB = Notation.initial
            , _ModuleName = "service-regression"
            , _QueryCallId = Just (Unique 0)
            }
        run premises active request = execUniqueT (runExceptT (runService env premises active request))
        failed (Right ServiceFailure) = True
        failed _ = False
        valueIs name expected (Right (ServiceContinue next _)) = bindVars (_TotalVarBinding next) (variable name) == expected
        valueIs _ _ _ = False
    huge <- run emptyArithStore context (Evaluate (variable x) (binary DC_mul (nat (10 ^ (40 :: Int))) (nat (10 ^ (40 :: Int)))))
    check "services preserve arbitrary-precision naturals" (valueIs x (nat (10 ^ (80 :: Int))) huge)
    partial <- run emptyArithStore context (Evaluate (variable x) (binary DC_div (nat 1) (nat 0)))
    check "division by zero fails the branch" (failed partial)
    underflow <- run emptyArithStore context (Evaluate (variable x) (binary DC_minus (nat 1) (nat 2)))
    check "natural subtraction underflow fails" (failed underflow)
    delayed <- run emptyArithStore context (Compare (DC DC_gt) [variable x, nat 0])
    case delayed of
        Right (ServiceContinue constrained _) -> do
            let bound = zonkLVar (VarBinding (Map.singleton x (nat 0))) constrained
            settled <- run emptyArithStore bound Settle
            check "later bindings recheck the residual arithmetic store" (failed settled)
        _ -> ioError (userError "linear unknown comparison was not retained")
    nonlinear <- run emptyArithStore context (Compare (DC DC_gt) [binary DC_mul (variable x) (variable y), nat 0])
    check "nonlinear unsupported comparison is an error rather than a residual" (case nonlinear of Left (UnsupportedArithmeticConstraint _) -> True; _ -> False)
    let proposition = binary DC_gt (variable x) (nat 0)
    guarded <- run ([proposition], []) context (Compare (DC DC_gt) [variable x, nat 0])
    check "active arithmetic premises discharge the same comparison" (case guarded of Right (ServiceContinue next _) -> not (any comparison (_LeftConstraints next)); _ -> False)
    let color = TyCon (TCon (TC_Named "color") Star)
        colored = context { _CurrentLabeling = labels { _NamedTypes = Map.singleton "X" color } }
    unification <- run emptyArithStore colored (Evaluate (variable x) (mkNCon (DC_Named "red")))
    check "non-arithmetic is requests native unification" (case unification of Right (ServiceUnify _ _ left right) -> left == variable x && right == mkNCon (DC_Named "red"); _ -> False)
    readNat <- run emptyArithStore context (Read [variable x])
    check "primitive input installs a typed natural binding" (valueIs x (nat 8) readNat)
    writeIORef input (Just (mkNCon (DC_ChrL 'a')))
    readWrong <- run emptyArithStore context (Read [variable x])
    check "primitive input checks type before installation" (failed readWrong)
    _ <- run emptyArithStore (zonkLVar (VarBinding (Map.singleton x (nat 9))) context) (Print [variable x])
    printed <- readIORef output
    check "print observes current native substitution" (printed == [nat 9])
    putStrLn "V1 host services: arithmetic, residual constraints, native-unify handoff and I/O passed"
    where
        comparison ArithmeticConstraint {} = True
        comparison _ = False
