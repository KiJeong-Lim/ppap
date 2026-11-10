module Main where

import Control.Monad
import Control.Monad.Trans.Except
import Control.Monad.Trans.Reader
import Control.Monad.Trans.State.Strict
import Control.Monad.Trans.Writer
import Data.IORef
import Data.Maybe (isNothing)
import Z.Utils

newtype Strided a
    = Strided { runStrided :: State Int a }
    deriving ()

instance Functor Strided where
    fmap f = Strided . fmap f . runStrided

instance Applicative Strided where
    pure = Strided . pure
    (<*>) = ap

instance Monad Strided where
    action >>= next = Strided (runStrided action >>= runStrided . next)

instance MonadUnique Strided where
    getUnique = Strided (state (\value -> (Unique value, value + 3)))

check :: String -> Bool -> IO ()
check label condition = unless condition (ioError (userError label))

required :: Maybe UniqueBlock -> IO UniqueBlock
required = maybe (ioError (userError "unique block allocation failed")) return

throughLayers :: ExceptT String (StateT Int (WriterT [String] (UniqueT IO))) (Maybe UniqueBlock)
throughLayers = getUniqueBlock 3

main :: IO ()
main = do
    ((zero, negative, reserved, next), final) <- return $ runState (runStrided custom) 7
    check "invalid default requests do not consume IDs" (isNothing zero && isNothing negative)
    block <- required reserved
    check "default blocks preserve noncontiguous allocator IDs" (map (`lookupUniqueBlock` block) [2, 0, 1] == map (Just . Unique) [13, 7, 10] && next == Unique 16 && final == 19)
    check "default block lookup is bounded" (isNothing (lookupUniqueBlock (-1) block) && isNothing (lookupUniqueBlock 3 block))

    (large, following) <- execUniqueT $ do
        result <- getUniqueBlock 100000
        next <- getUnique
        return (result, next)
    affine <- required large
    check "large UniqueT blocks support later lookup of earlier IDs" (map (`lookupUniqueBlock` affine) [99999, 0, 50000] == map (Just . Unique) [99999, 0, 50000] && following == Unique 100000)
    check "UniqueT block lookup is bounded" (isNothing (lookupUniqueBlock (-1) affine) && isNothing (lookupUniqueBlock 100000 affine))

    boundary <- newIORef (maxBound - 1)
    rejected <- runReaderT (runUniqueT (getUniqueBlock 2)) boundary
    unchanged <- readIORef boundary
    lastBlock <- runReaderT (runUniqueT (getUniqueBlock 1)) boundary >>= required
    exhausted <- runReaderT (runUniqueT (getUniqueBlock 1)) boundary
    finalCounter <- readIORef boundary
    check "overflow leaves the allocator unchanged" (isNothing rejected && unchanged == maxBound - 1)
    check "last representable next counter remains valid" (lookupUniqueBlock 0 lastBlock == Just (Unique (maxBound - 1)) && isNothing exhausted && finalCounter == maxBound)
    invalid <- newIORef (-1)
    invalidBlock <- runReaderT (runUniqueT (getUniqueBlock 1)) invalid
    invalidCounter <- readIORef invalid
    check "negative allocator state is rejected without mutation" (isNothing invalidBlock && invalidCounter == -1)
    empty <- newIORef 12
    rejectedCounts <- runReaderT (runUniqueT (mapM getUniqueBlock [0, -1, minBound])) empty
    unchangedEmpty <- readIORef empty
    check "invalid UniqueT counts are rejected without mutation" (all isNothing rejectedCounts && unchangedEmpty == 12)

    (layers, afterLayers) <- execUniqueT $ do
        result <- runWriterT (runStateT (runExceptT throughLayers) 42)
        next <- getUnique
        return (result, next)
    case layers of
        ((Right (Just lifted), 42), []) -> check "transformer layers preserve reservation and state" (lookupUniqueBlock 2 lifted == Just (Unique 2) && afterLayers == Unique 3)
        _ -> ioError (userError "unique block transformer lifting failed")
    putStrLn "Unique blocks: custom allocation, large reservations, overflow and transformer lifting passed"
    where
        custom = do
            zero <- getUniqueBlock 0
            negative <- getUniqueBlock (-1)
            reserved <- getUniqueBlock 3
            next <- getUnique
            return (zero, negative, reserved, next)
