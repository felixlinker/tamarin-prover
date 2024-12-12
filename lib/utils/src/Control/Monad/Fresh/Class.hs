-- |
-- Copyright   : (c) 2010 Simon Meier
-- License     : GPL v3 (see LICENSE)
--
-- Portability : portable
--
-- Type-class abstracting computations that need a fresh name supply.
module Control.Monad.Fresh.Class (
  MonadFresh(..)
) where

-- import Control.Basics

import Control.Monad.Trans
import Control.Monad.Trans.Maybe
import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Writer
import qualified Data.Map as M

import qualified Control.Monad.Trans.PreciseFresh as Precise
import Control.Monad.RWS (RWST (RWST, runRWST))

-- Added 'Applicative' until base states this hierarchy
class (Applicative m, Monad m) => MonadFresh m where
    -- | Get the integer of the next fresh identifier of this name.
    freshIdent  :: String   -- ^ Desired name
                -> m Integer

    -- | Get a number of fresh identifiers. This reserves the required number
    -- of identifiers on all names.
    freshIdents :: M.Map String Integer -- ^ Number of desired fresh identifiers by name.
                -> m (M.Map String Integer) -- ^ The first Fresh identifiers.

    -- | Scope the 'freshIdent' and 'freshIdents' requests such that these
    -- variables are not marked as used once the scope is left.
    scopeFreshness :: m a -> m a

instance Monad m => MonadFresh (Precise.FreshT m) where
    freshIdent     = Precise.freshIdent
    freshIdents    = Precise.freshIdents
    scopeFreshness = Precise.scopeFreshness


----------------------------------------------------------------------------
-- instances for other mtl transformers
--
-- TODO: Add remaining ones

instance MonadFresh m => MonadFresh (MaybeT m) where
    freshIdent       = lift . freshIdent
    freshIdents      = lift . freshIdents
    scopeFreshness m = MaybeT $ scopeFreshness (runMaybeT m)

instance MonadFresh m => MonadFresh (StateT s m) where
    freshIdent  = lift . freshIdent
    freshIdents = lift . freshIdents
    scopeFreshness m = StateT $ \s -> scopeFreshness (runStateT m s)

instance MonadFresh m => MonadFresh (ReaderT r m) where
    freshIdent       = lift . freshIdent
    freshIdents      = lift . freshIdents
    scopeFreshness m = ReaderT $ \r -> scopeFreshness (runReaderT m r)

instance (Monoid w, MonadFresh m) => MonadFresh (WriterT w m) where
    freshIdent       = lift . freshIdent
    freshIdents      = lift . freshIdents
    scopeFreshness m = WriterT $ scopeFreshness (runWriterT m)

instance (Monoid w, MonadFresh m) => MonadFresh (RWST r w s m) where
    freshIdent       = lift . freshIdent
    freshIdents      = lift . freshIdents
    scopeFreshness m = RWST $ \r s -> scopeFreshness (runRWST m r s)
