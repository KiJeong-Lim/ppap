module Jasmine.Alpha2.Header.Export
    ( UniqueGenT, UniqueLike (..), runUniqueGenT
    , module Control.Monad.IO.Class
    , module Control.Monad.Trans.Class
    , module Control.Monad.Trans.State.Strict
    , module Jasmine.Alpha2.Header.TermNode
    ) where

import Control.Monad.IO.Class
import Control.Monad.Trans.Class
import Control.Monad.Trans.State.Strict
import Jasmine.Alpha2.Header.TermNode

newtype UniqueGenT m a
    = UniqueGenT { unUniqueGenT :: StateT Integer m a }
    deriving ()

class Eq u => UniqueLike u where
    genUnique :: Monad m => UniqueGenT m u

instance UniqueLike (Integer) where
    genUnique = UniqueGenT go where
        go :: (Enum u, Monad m) => StateT u m u
        go = do
            u <- get
            let u' = succ u
            u' `seq` put u'
            return u'

instance Functor f => Functor (UniqueGenT f) where
    fmap f = UniqueGenT . fmap f . unUniqueGenT

instance Monad m => Applicative (UniqueGenT m) where
    pure = UniqueGenT . pure
    mf <*> mx = UniqueGenT (unUniqueGenT mf <*> unUniqueGenT mx)

instance Monad m => Monad (UniqueGenT m) where
    m >>= k = UniqueGenT (unUniqueGenT m >>= unUniqueGenT . k)

instance MonadTrans (UniqueGenT) where
    lift = UniqueGenT . lift

instance MonadIO m => MonadIO (UniqueGenT m) where
    liftIO = lift . liftIO

runUniqueGenT :: Functor f => UniqueGenT f a -> f a
runUniqueGenT = fmap fst . flip runStateT 0 . unUniqueGenT
