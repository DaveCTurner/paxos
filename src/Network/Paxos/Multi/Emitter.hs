{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}

module Network.Paxos.Multi.Emitter
  ( EmitterT
  , runEmitterT
  , execEmitterT
  ) where

import qualified Data.DList as DL
import Control.Applicative
import Control.Monad.Writer
import Control.Monad.State

import Network.Paxos.Multi.Types

newtype EmitterT w s m a = EmitterT (WriterT (DL.DList w) (StateT s m) a)
  deriving (Functor, Applicative, Monad)

instance MonadTrans (EmitterT w s) where
  lift = EmitterT . lift . lift

instance Monad m => MonadState s (EmitterT w s m) where

instance Monad m => MonadEmitter (EmitterT w s m) where
  type Emitted (EmitterT w s m) = w
  emit = EmitterT . tell . DL.singleton

runEmitterT :: Monad m => EmitterT w s m a -> s -> m (a, [w], s)
runEmitterT (EmitterT go) s = do
  ((a,dw),s') <- runStateT (runWriterT go) s
  return (a, DL.toList dw, s')

execEmitterT :: Monad m => EmitterT w s m a -> s -> m ([w], s)
execEmitterT go s = liftM (\(_,w,s') -> (w,s')) $ runEmitterT go s
