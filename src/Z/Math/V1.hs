module Z.Math.V1 where

import Control.Applicative
import Control.Monad.Trans.State.Strict
import Data.Function
import qualified Data.List as List
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Ratio
import Y.Base
import Z.Algo.Function
import Z.Math.Classes
import Z.Math.V1.Internal
import Z.Text.PC

type EvalEnv val = [(ExprCall, ElemExpr val)]

data ElemExpr val
    = PluEE (ElemExpr val) (ElemExpr val)
    | NegEE (ElemExpr val)
    | MulEE (ElemExpr val) (ElemExpr val)
    | PosEE (PositiveInteger)
    | LitEE (val)
    | VarEE (VarID)
    | AppEE (ElemExpr val) (ElemExpr val)
    deriving (Eq)

instance (Show val, Fractional val) => Show (CoreExpr val) where
    showsPrec prec = showsPrec prec . fromCore (Map.fromList [ (i, VarEE ("x" ++ show i)) | i <- [0, 1 .. 100] ])

instance Show val => Show (ElemExpr val) where
    showsPrec prec = dispatch where
        myPrecIs :: Int -> ShowS -> ShowS
        myPrecIs prec' ss = if prec > prec' then strstr "(" . ss . strstr ")" else ss
        dispatch :: Show val => ElemExpr val -> ShowS
        dispatch (PluEE e1 (NegEE e2)) = myPrecIs 4 (showsPrec 4 e1 . strstr " - " . showsPrec 5 e2)
        dispatch (PluEE e1 e2) = myPrecIs 4 (showsPrec 4 e1 . strstr " + " . showsPrec 5 e2)
        dispatch (NegEE e1) = myPrecIs 6 (strstr "- " . showsPrec 6 e1)
        dispatch (MulEE e1 e2) = myPrecIs 5 (showsPrec 5 e1 . strstr " * " . showsPrec 6 e2)
        dispatch (PosEE n) = myPrecIs 11 (shows n)
        dispatch (LitEE val) = myPrecIs 11 (shows val)
        dispatch (VarEE var) = myPrecIs 11 (strstr var)
        dispatch e = fromJust (tryMatchPrimitive e /> return (showsAppEE (unfoldAppEE e)))
        tryMatchPrimitive :: Show val => ElemExpr val -> Maybe ShowS
        tryMatchPrimitive (AppEE (VarEE unary_operator) e1) = lookup unary_operator
            [ ("_ABS_", myPrecIs 11 (strstr "| " . showsPrec 0 e1 . strstr " |"))
            ]
        tryMatchPrimitive (AppEE (AppEE (VarEE binary_operator) e1) e2) = lookup binary_operator
            [ ("_DIV_", myPrecIs 5 (showsPrec 5 e1 . strstr " / " . showsPrec 6 e2))
            ]
        tryMatchPrimitive _ = Nothing
        unfoldAppEE :: ElemExpr val -> (ElemExpr val, [ElemExpr val])
        unfoldAppEE = flip go [] where
            go :: ElemExpr val -> [ElemExpr val] -> (ElemExpr val, [ElemExpr val])
            go (AppEE e1 e2) es = go e1 (e2 : es)
            go e es = (e, es)
        showsAppEE :: Show val => (ElemExpr val, [ElemExpr val]) -> ShowS
        showsAppEE (e, es) = showsPrec 9 e . strstr "(" . ppunc ", " (map (showsPrec 0) es) . strstr ")"

instance Functor (ElemExpr) where
    fmap f (PluEE e1 e2) = PluEE (fmap f e1) (fmap f e2)
    fmap f (NegEE e1) = NegEE (fmap f e1)
    fmap f (MulEE e1 e2) = MulEE (fmap f e1) (fmap f e2)
    fmap f (PosEE n) = PosEE n
    fmap f (LitEE val) = LitEE (f val)
    fmap f (VarEE var) = VarEE var
    fmap f (AppEE e1 e2) = AppEE (fmap f e1) (fmap f e2)

instance Num val => Num (ElemExpr val) where
    e1 + e2 = e1 `seq` e2 `seq` PluEE e1 e2
    e1 - e2 = e1 `seq` e2 `seq` PluEE e1 (NegEE e2)
    e1 * e2 = e1 `seq` e2 `seq` MulEE e1 e2
    negate e1 = e1 `seq` NegEE e1
    abs e1 = e1 `seq` AppEE (VarEE "_ABS_") e1
    signum e1 = e1 `seq` AppEE (AppEE (VarEE "_DIV_") e1) (AppEE (VarEE "_ABS_") e1)
    fromInteger n
        = case n `compare` 0 of
            (LT) -> NegEE (PosEE (abs n))
            (EQ) -> VarEE "0"
            (GT) -> PosEE (abs n)

instance Fractional val => Fractional (ElemExpr val) where
    fromRational r = AppEE (AppEE (VarEE "_DIV_") (fromInteger (numerator r))) (fromInteger (denominator r))
    recip e1 = e1 `seq` AppEE (AppEE (VarEE "_DIV_") 1) e1
    e1 / e2 = e1 `seq` e2 `seq` AppEE (AppEE (VarEE "_DIV_") e1) e2

instance IsExpr (ElemExpr) where
    evalExpr = evalElemExpr
    reduceExpr = reduceElemExpr
    embed = LitEE
    var = VarEE
    getExprRep = showsPrec 0

evalElemExprWith :: Num val => (EvalEnv val -> ElemExpr val -> ErrMsgM val) -> EvalEnv val -> ElemExpr val -> val
evalElemExprWith = go where
    go :: Num val => (EvalEnv val -> ElemExpr val -> ErrMsgM val) -> EvalEnv val -> ElemExpr val -> val
    go wild_card env (PluEE e1 e2) = (go wild_card env e1) + (go wild_card env e2)
    go wild_card env (NegEE e1) = negate (go wild_card env e1)
    go wild_card env (MulEE e1 e2) = (go wild_card env e1) * (go wild_card env e2)
    go wild_card env (PosEE n) = fromInteger n
    go wild_card env (LitEE v) = v
    go wild_card env (VarEE "0") = 0
    go wild_card env e = fromErrMsgM (wild_card env e)

evalElemExpr :: Fractional val => EvalEnv val -> ElemExpr val -> val
evalElemExpr = evalElemExprWith myWildCard where
    myWildCard :: Fractional val => EvalEnv val -> ElemExpr val -> ErrMsgM val
    myWildCard env e = addErrMsg "evalElemExpr" (tryMatchPrimitive env e /> callWith e [] env)
    tryMatchPrimitive :: Fractional val => EvalEnv val -> ElemExpr val -> Maybe val
    tryMatchPrimitive env (VarEE "0+") = return (1 / _INF_)
    tryMatchPrimitive env (VarEE "0-") = return (negate 1 / _INF_)
    tryMatchPrimitive env (VarEE "_INF_") = return _INF_
    tryMatchPrimitive env (AppEE (VarEE "_ABS_") e1) = return (abs (evalElemExpr env e1))
    tryMatchPrimitive env (AppEE (AppEE (VarEE "_DIV_") e1) e2) = return (evalElemExpr env e1 / evalElemExpr env e2)
    tryMatchPrimitive env _ = Nothing
    getDefn :: VarID -> Int -> EvalEnv val -> Maybe ([ExprCall], ElemExpr val)
    getDefn f_lookedup xs_len env = safehd [ (xs, body) | (SApp f xs, body) <- env, f == f_lookedup, length xs == xs_len ]
    callWith :: Fractional val => ElemExpr val -> [ElemExpr val] -> EvalEnv val -> Maybe val
    callWith (AppEE e1 e2) es env = callWith e1 (e2 : es) env
    callWith (VarEE x) es env = do
        (params, body) <- getDefn x (length es) env
        let new_env = zip params es ++ env
        return (evalElemExpr new_env body)
    callWith _ es env = Nothing

reduceElemExpr :: (Eq val, Fractional val) => ReductionOption -> ElemExpr val -> ElemExpr val
reduceElemExpr option
    | option == ReduceLv1 = reduce
    | option == ReduceLv2 = reduceElemExprAsFraction . reduce
    where
        myPlu :: (Eq val, Fractional val) => ElemExpr val -> ElemExpr val -> ElemExpr val
        myPlu (LitEE val1) (LitEE val2) = myLit (val1 + val2)
        myPlu (LitEE 0) e2 = e2
        myPlu e1 (LitEE 0) = e1
        myPlu e1 e2 = PluEE e1 e2
        myNeg :: (Eq val, Fractional val) => ElemExpr val -> ElemExpr val
        myNeg (LitEE val1) = myLit (negate val1)
        myNeg e1 = NegEE e1
        myMul :: (Eq val, Fractional val) => ElemExpr val -> ElemExpr val -> ElemExpr val
        myMul (LitEE val1) (LitEE val2) = myLit (val1 * val2)
        myMul (LitEE val1) e2
            | val1 == 1 = e2
            | val1 == 0 = myLit 0
            | val1 == negate 1 = myNeg e2
        myMul e1 (LitEE val2)
            | val2 == 1 = e1
            | val2 == 0 = myLit 0
            | val2 == negate 1 = myNeg e1
        myMul e1 e2 = MulEE e1 e2
        myDiv :: (Eq val, Fractional val) => ElemExpr val -> ElemExpr val -> ElemExpr val
        myDiv (LitEE val1) (LitEE val2) = myLit (val1 / val2)
        myDiv (LitEE val1) e2
            | val1 == 1 = AppEE (AppEE (VarEE "_DIV_") (myLit 1)) e2
            | val1 == 0 = myLit 0
            | val1 == negate 1 = AppEE (AppEE (VarEE "_DIV_") (myLit 1)) (myNeg e2)
        myDiv e1 (LitEE val2)
            | val2 == 1 = e1
            | val2 == 0 = error "divided by 0"
            | val2 == negate 1 = myNeg e1
        myDiv e1 e2 = AppEE (AppEE (VarEE "_DIV_") e1) e2
        myLit :: val -> ElemExpr val
        myLit val = val `seq` LitEE val
        reduce :: (Eq val, Fractional val) => ElemExpr val -> ElemExpr val
        reduce (PluEE e1 e2) = myPlu (reduce e1) (reduce e2)
        reduce (NegEE e1) = myNeg (reduce e1)
        reduce (MulEE e1 e2) = myMul (reduce e1) (reduce e2)
        reduce (PosEE num) = myLit (fromInteger num)
        reduce (LitEE val) = myLit val
        reduce (VarEE "0") = myLit (fromInteger 0)
        reduce (AppEE (AppEE (VarEE "_DIV_") e1) e2) = myDiv (reduce e1) (reduce e2)
        reduce (AppEE e1 e2) = AppEE (reduce e1) (reduce e2)
        reduce e = e

toCore :: (Eq val, Num val) => ElemExpr val -> (Map.Map IVar (ElemExpr val), CoreExpr val)
toCore = fromJust . go where
    loop :: (Eq val, Num val) => ElemExpr val -> StateT [ElemExpr val] Maybe (CoreExpr val)
    loop (PluEE e1 e2) = do
        e1' <- loop e1
        e2' <- loop e2
        return (mkPluCE e1' e2')
    loop (NegEE e1) = do
        e1' <- loop e1
        return (mkNegCE e1')
    loop (MulEE e1 e2) = do
        e1' <- loop e1
        e2' <- loop e2
        return (mkMulCE e1' e2')
    loop (PosEE n) = return (mkIntCE n)
    loop (LitEE v) = return (mkLitCE v)
    loop (VarEE "0") = return (mkIntCE 0)
    loop (AppEE (AppEE (VarEE "_DIV_") e1) e2) = do
        e1' <- loop e1
        e2' <- loop e2
        return (mkDivCE e1' e2')
    loop e = do
        es <- get
        case e `List.elemIndex` es of
            Nothing -> do
                put (es ++ [e])
                return (VarCE (length es))
            Just x -> return (VarCE x)
    go :: (Eq val, Num val) => ElemExpr val -> Maybe (Map.Map IVar (ElemExpr val), CoreExpr val)
    go e = do
        (e', vars) <- runStateT (loop e) []
        return (Map.fromAscList (zip [0, 1 ..] vars), e')

fromCore :: (Fractional val) => Map.Map IVar (ElemExpr val) -> CoreExpr val -> ElemExpr val
fromCore env (VarCE x) = fromJust (Map.lookup x env)
fromCore env (ValCE v) = either fromInteger embed (fromValue v)
fromCore env (PluCE e1 (NegCE e2)) = fromCore env e1 - fromCore env e2
fromCore env (PluCE e1 e2) = fromCore env e1 + fromCore env e2
fromCore env (NegCE e1) = negate (fromCore env e1)
fromCore env (MulCE e1 (InvCE e2)) = fromCore env e1 / fromCore env e2
fromCore env (MulCE e1 e2) = fromCore env e1 * fromCore env e2
fromCore env (InvCE e1) = recip (fromCore env e1)

reduceElemExprAsFraction :: (Eq val, Fractional val) => ElemExpr val -> ElemExpr val
reduceElemExprAsFraction = uncurry fromCore . fmap reduceCoreToFraction . toCore

readElemExpr :: String -> ElemExpr Double
readElemExpr = either error id . runPC "<interactive>" (pcMain 0) where
    pcVarEE :: PC (ElemExpr Double)
    pcVarEE = do
        var <- regexPC "[\'a\'-\'z\' \'A\'-\'Z\'] [\'a\'-\'z\' \'A\'-\'Z\' \'0\'-\'9\' \'_\']*"
        return (VarEE var)
    pcPosEE :: PC (ElemExpr Double)
    pcPosEE = do
        num <- pure read <*> regexPC "[\'0\'-\'9\']+"
        return (PosEE num)
    pcLitEE :: PC (ElemExpr Double)
    pcLitEE = do
        val <- pure read <*> regexPC "[\'0\'-\'9\']+ \".\" [\'0\'-\'9\']+"
        return (LitEE val)
    pcSuffix :: Int -> PC (ElemExpr Double -> ElemExpr Double)
    pcSuffix 0 = mconcat
        [ do
            consumePC " + "
            e2 <- pcMain 1
            e2 `seq` return (\e1 -> PluEE e1 e2)
        , do
            consumePC " - "
            e2 <- pcMain 1
            e2 `seq` return (\e1 -> PluEE e1 (NegEE e2))
        ]
    pcSuffix 1 = mconcat
        [ do
            consumePC " * "
            e2 <- pcMain 2
            e2 `seq` return (\e1 -> MulEE e1 e2)
        , do
            consumePC " / "
            e2 <- pcMain 2
            e2 `seq` return (\e1 -> AppEE (AppEE (VarEE "_DIV_") e1) e2)
        ]
    pcSuffix _ = empty
    pcMain :: Int -> PC (ElemExpr Double)
    pcMain 0 = pure (List.foldl' (&)) <*> pcMain 1 <*> many (pcSuffix 0)
    pcMain 1 = pure (List.foldl' (&)) <*> pcMain 2 <*> many (pcSuffix 1)
    pcMain 2 = mconcat
        [ do
            consumePC "+ "
            e1 <- pcMain 2
            e1 `seq` return e1
        , do
            consumePC "- "
            e1 <- pcMain 2
            e1 `seq` return (NegEE e1)
        , pcMain 3
        ]
    pcMain 3 = mconcat
        [ do
            fun <- pcVarEE
            consumePC "("
            args <- pure [] <|> (pure (:) <*> pcMain 0 <*> many (consumePC ", " *> pcMain 0))
            consumePC ")"
            return (List.foldl' AppEE fun args)
        , pcMain 4
        ]
    pcMain 4 = mconcat
        [ pcVarEE
        , pcLitEE
        , pcPosEE
        , consumePC "(" *> pcMain 0 <* consumePC ")"
        ]
