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
    , UniqueMakerT
    , HasSrcLoc (..)
    , HasAnnotation (..)
    , GeneratingUniqueMonad (..)
    , mkSrcLoc
    , runUniqueMakerT
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

mkSrcLoc :: SrcPos -> SrcPos -> SrcLoc
mkSrcLoc pos1 pos2 = if pos1 < pos2 then SrcLoc { _BegPos = pos1, _EndPos = pos2 } else SrcLoc { _BegPos = pos2, _EndPos = pos1 }

runUniqueMakerT :: Functor m => UniqueMakerT m a -> m a
runUniqueMakerT = fmap fst . flip runStateT 0 . unUniqueMakerT
