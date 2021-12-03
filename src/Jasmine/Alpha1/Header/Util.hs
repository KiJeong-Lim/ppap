module Jasmine.Alpha1.Header.Util where

import Control.Applicative
import Control.Monad.IO.Class
import Control.Monad.Trans.Class
import Control.Monad.Trans.Except
import Control.Monad.Trans.State.Strict
import Data.Function
import qualified Data.List as List
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Y.Base
import Z.Algo.Function (MyNat)
import Z.Text.Doc
import Z.Text.PC

type SrcRow = Int

type SrcCol = Int

type SrcPos = (SrcRow, SrcCol)

type LargeId = String

type SmallId = String

type Keyword = String

type ModName = String

type MyIVar = MyNat

data SrcLoc
    = SrcLoc
        { _BegPos :: SrcPos
        , _EndPos :: SrcPos
        }
    deriving (Eq, Ord)

data DataConstructor
    = DC_Unique Unique
    | DC_NatLit MyNat
    | DC_ChrLit Char
    | DC_SuccOf
    deriving (Eq, Ord, Show)

data TypeConstructor
    = TC_Atom Unique
    | TC_Type
    | TC_Prop
    | TC_Bang
    | TC_List
    | TCarrow
    deriving (Eq, Ord, Show)

data LambdaTerm con
    = Var (MyIVar)
    | Con (con)
    | App (LambdaTerm con) (LambdaTerm con)
    | Lam (MyIVar) (LambdaTerm con)
    | Fix (MyIVar) (LambdaTerm con)
    deriving (Eq, Ord)

data ReduceOption
    = ALPHA
    | WHNF
    | HNF
    | NF
    deriving (Eq)

newtype Unique
    = Unique { asInteger :: Integer }
    deriving (Eq, Ord)

newtype UniqueMakerT m a
    = UniqueMakerT { unUniqueMakerT :: StateT Integer m a }
    deriving ()

class HasSrcLoc a where
    getSrcLoc :: a -> SrcLoc

class HasAnnotation f where
    getAnnotation :: f a -> a

class Monad m => GeneratingUniqueMonad m where
    getNewUnique :: m Unique

instance Functor m => Functor (UniqueMakerT m) where
    fmap f = UniqueMakerT . fmap f . unUniqueMakerT

instance Monad m => Applicative (UniqueMakerT m) where
    pure x = UniqueMakerT (pure x)
    mf <*> mx = UniqueMakerT (unUniqueMakerT mf <*> unUniqueMakerT mx)

instance Monad m => Monad (UniqueMakerT m) where
    m >>= k = UniqueMakerT (unUniqueMakerT m >>= unUniqueMakerT . k)

instance Show (SrcLoc) where
    showsPrec = const . curry snd

instance Show (Unique) where
    showsPrec = const (shows . asInteger)

instance Semigroup (SrcLoc) where
    SrcLoc { _BegPos = beg1, _EndPos = end1 } <> SrcLoc { _BegPos = beg2, _EndPos = end2 } = mkSrcLoc (beg1 `min` beg2) (end1 `max` end2)

instance GeneratingUniqueMonad m => GeneratingUniqueMonad (ExceptT s m) where
    getNewUnique = lift getNewUnique

instance GeneratingUniqueMonad m => GeneratingUniqueMonad (StateT s m) where
    getNewUnique = lift getNewUnique

instance MonadTrans UniqueMakerT where
    lift = UniqueMakerT . lift

instance MonadIO m => MonadIO (UniqueMakerT m) where
    liftIO = UniqueMakerT . liftIO

instance PrettyPrintable (SrcLoc) where
    pretty prec (SrcLoc (beg_row, beg_col) (end_row, end_col))
        | beg_row == end_row = pparen (prec >= 5) "(" ")" $ pp beg_row <> pstr ":" <> pp beg_col <> pstr "-" <> pp end_col
        | otherwise = pparen (prec >= 5) "(" ")" $ pp beg_row <> pstr ":" <> pp beg_col <> pstr "-" <> pp end_row <> pstr ":" <> pp end_col

instance HasSrcLoc (SrcLoc) where
    getSrcLoc = id

instance Monad m => GeneratingUniqueMonad (UniqueMakerT m) where
    getNewUnique = UniqueMakerT $ do
        n <- get
        let n' = succ n
        n' `seq` put n'
        return (Unique { asInteger = n' })

instance Show con => Show (LambdaTerm con) where
    showsPrec prec = dispatch where
        myPrecIs :: Int -> ShowS -> ShowS
        myPrecIs prec' ss = if prec > prec' then strstr "(" . ss . strstr ")" else ss
        showsVar :: MyIVar -> ShowS
        showsVar x = strstr "x" . shows x
        dispatch :: Show con => LambdaTerm con -> ShowS
        dispatch (Var x) = showsVar x
        dispatch (Con c) = shows c
        dispatch (App t1 t2) = myPrecIs 10 $ showsPrec 10 t1 . strstr " " . showsPrec 11 t2
        dispatch (Lam y t1) = myPrecIs 0 $ strstr "\\" . showsVar y . strstr " -> " . showsPrec 0 t1

instance Functor (LambdaTerm) where
    fmap modify_c (Var x) = Var x
    fmap modify_c (Con c) = Con (modify_c c)
    fmap modify_c (App t1 t2) = App (fmap modify_c t1) (fmap modify_c t2)
    fmap modify_c (Lam y t1) = Lam y (fmap modify_c t1)

mkSrcLoc :: SrcPos -> SrcPos -> SrcLoc
mkSrcLoc pos1 pos2 = if pos1 < pos2 then SrcLoc { _BegPos = pos1, _EndPos = pos2 } else SrcLoc { _BegPos = pos2, _EndPos = pos1 }

runUniqueMakerT :: Functor m => UniqueMakerT m a -> m a
runUniqueMakerT = fmap fst . flip runStateT 0 . unUniqueMakerT

getFVsOfLambdaTerm :: LambdaTerm con -> Set.Set MyIVar
getFVsOfLambdaTerm = flip go Set.empty where
    go :: LambdaTerm con -> Set.Set MyIVar -> Set.Set MyIVar
    go (Var x) = Set.insert x
    go (Con c) = id
    go (App t1 t2) = go t1 . go t2
    go (Lam y t1) = Set.union (y `Set.delete` getFVsOfLambdaTerm t1)
    go (Fix f e) = Set.union (f `Set.delete` getFVsOfLambdaTerm e)

substituteLambdaTerm :: [(MyIVar, LambdaTerm con)] -> LambdaTerm con -> LambdaTerm con
substituteLambdaTerm = flip substitute . foldr conssubst nilsubst where
    chi :: (MyIVar -> LambdaTerm con) -> LambdaTerm con -> MyIVar
    chi sigma = succ . maybe 0 id . Set.lookupMax . Set.unions . Set.map (getFVsOfLambdaTerm . sigma) . getFVsOfLambdaTerm
    nilsubst :: (MyIVar -> LambdaTerm con)
    nilsubst = Var
    conssubst :: (MyIVar, LambdaTerm con) -> (MyIVar -> LambdaTerm con) -> (MyIVar -> LambdaTerm con)
    conssubst (z, t) sigma x = if z == x then t else sigma x
    substitute :: LambdaTerm con -> (MyIVar -> LambdaTerm con) -> LambdaTerm con
    substitute (Var x) = substituteVar x
    substitute (Con c) = substituteCon c
    substitute (App t1 t2) = substituteApp t1 t2
    substitute t = substituteFun t <*> flip chi t
    substituteVar :: MyIVar -> (MyIVar -> LambdaTerm con) -> LambdaTerm con
    substituteVar = (&)
    substituteCon :: con -> (MyIVar -> LambdaTerm con) -> LambdaTerm con
    substituteCon = pure . Con
    substituteApp :: LambdaTerm con -> LambdaTerm con -> (MyIVar -> LambdaTerm con) -> LambdaTerm con
    substituteApp t1 t2 = pure App <*> substitute t1 <*> substitute t2
    substituteFun :: LambdaTerm con -> (MyIVar -> LambdaTerm con) -> MyIVar -> LambdaTerm con
    substituteFun (Lam y t1) sigma z = Lam z (substitute t1 (conssubst (y, Var z) sigma))
    substituteFun (Fix f e) sigma z = Fix z (substitute e (conssubst (f, Var z) sigma))

evalLambdaTerm :: ReduceOption -> LambdaTerm con -> LambdaTerm con
evalLambdaTerm option (App (Lam y t1) t2) = evalLambdaTerm option (substituteLambdaTerm [(y, t2)] t1)
evalLambdaTerm option (Var x) = Var x
evalLambdaTerm option (Con c) = Con c
evalLambdaTerm option (App t1 t2) = App (evalLambdaTerm option t1) (if option == NF then evalLambdaTerm option t2 else t2)
evalLambdaTerm option (Lam y t1) = if option == WHNF then Lam y t1 else Lam y (evalLambdaTerm option t1)
evalLambdaTerm option (Fix f e) = evalLambdaTerm option (substituteLambdaTerm [(f, Fix f e)] e)

readLambdaTerm :: String -> LambdaTerm DataConstructor
readLambdaTerm = either error id . runPC "<readLambdaTerm>" (pcLambdaTerm 0) where
    pcVar :: PC MyIVar
    pcVar = consumePC "x" *> (pure read <*> regexPC "['0'-'9'] + ['1'-'9'] ['0'-'9']+")
    pcCon :: PC DataConstructor
    pcCon = consumePC "c" *> (pure (DC_Unique . Unique . read) <*> regexPC "['0'-'9'] + ['1'-'9'] ['0'-'9']+")
    pcLambdaTerm :: Int -> PC (LambdaTerm DataConstructor)
    pcLambdaTerm 0 = mconcat
        [ do
            consumePC "\\"
            y <- pcVar
            consumePC " -> "
            t1 <- pcLambdaTerm 0
            return (Lam y t1)
        , do
            consumePC "fix "
            f <- pcVar
            consumePC " := "
            e <- pcLambdaTerm 0
            return (Fix f e)
        , pcLambdaTerm 1
        ]
    pcLambdaTerm 1 = pure (List.foldl' App) <*> pcLambdaTerm 2 <*> many (consumePC " " *> pcLambdaTerm 2)
    pcLambdaTerm 2 = mconcat
        [ pure Var <*> pcVar
        , pure Con <*> pcCon
        , consumePC "(" *> pcLambdaTerm 0 <* consumePC ")"
        ]
