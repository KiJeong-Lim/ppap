module Jasmine.Alpha1.Header.Util
    ( SrcRow
    , SrcCol
    , SrcPos
    , LargeId
    , SmallId
    , Keyword
    , ModName
    , SrcLoc (_BegPos, _EndPos)
    , Unique
    , UniqueT
    , HasSrcLoc (..)
    , HasAnnotation (..)
    , GeneratingUniqueMonad (..)
    , mkSrcLoc
    , runUniqueT
    ) where

import Control.Monad.IO.Class
import Control.Monad.Trans.Class
import Control.Monad.Trans.Except
import Control.Monad.Trans.State.Strict
import Data.Function
import Z.Text.Doc

type SrcRow = Int

type SrcCol = Int

type SrcPos = (SrcRow, SrcCol)

type LargeId = String

type SmallId = String

type Keyword = String

type ModName = String

data SrcLoc
    = SrcLoc
        { _BegPos :: SrcPos
        , _EndPos :: SrcPos
        }
    deriving (Eq, Ord)

newtype Unique
    = Unique { asInteger :: Integer }
    deriving (Eq, Ord)

newtype UniqueT m a
    = UniqueT { unUniqueT :: StateT Integer m a }
    deriving ()

class HasSrcLoc a where
    getSrcLoc :: a -> SrcLoc

class HasAnnotation f where
    getAnnotation :: f a -> a

class Monad m => GeneratingUniqueMonad m where
    getNewUnique :: m Unique

instance Functor m => Functor (UniqueT m) where
    fmap f = UniqueT . fmap f . unUniqueT

instance Monad m => Applicative (UniqueT m) where
    pure x = UniqueT (pure x)
    mf <*> mx = UniqueT (unUniqueT mf <*> unUniqueT mx)

instance Monad m => Monad (UniqueT m) where
    m >>= k = UniqueT (unUniqueT m >>= unUniqueT . k)

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

instance MonadTrans UniqueT where
    lift = UniqueT . lift

instance MonadIO m => MonadIO (UniqueT m) where
    liftIO = UniqueT . liftIO

instance PrettyPrintable (SrcLoc) where
    pretty prec (SrcLoc (beg_row, beg_col) (end_row, end_col))
        | beg_row == end_row = pparen (prec >= 5) "(" ")" $ pp beg_row <> pstr ":" <> pp beg_col <> pstr "-" <> pp end_col
        | otherwise = pparen (prec >= 5) "(" ")" $ pp beg_row <> pstr ":" <> pp beg_col <> pstr "-" <> pp end_row <> pstr ":" <> pp end_col

instance HasSrcLoc (SrcLoc) where
    getSrcLoc = id

instance Monad m => GeneratingUniqueMonad (UniqueT m) where
    getNewUnique = UniqueT $ do
        n <- get
        let n' = succ n
        n' `seq` put n'
        return (Unique { asInteger = n' })

mkSrcLoc :: SrcPos -> SrcPos -> SrcLoc
mkSrcLoc pos1 pos2 = if pos1 < pos2 then SrcLoc { _BegPos = pos1, _EndPos = pos2 } else SrcLoc { _BegPos = pos2, _EndPos = pos1 }

runUniqueT :: Functor m => UniqueT m a -> m a
runUniqueT = fmap fst . flip runStateT 0 . unUniqueT
