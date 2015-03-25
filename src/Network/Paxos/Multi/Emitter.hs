{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}

module Network.Paxos.Multi.Emitter where

import qualified Data.DList as DL
import Control.Arrow
import Control.Applicative
import Control.Monad.Writer

import Network.Paxos.Multi.Types

newtype EmitterT w m a = EmitterT (WriterT (DL.DList w) m a)
  deriving (Functor, Applicative, Monad)

instance Monad m => MonadEmitter w (EmitterT w m) where
  emit = EmitterT . tell . DL.singleton

runEmitterT :: Monad m => EmitterT w m a -> m (a, [w])
runEmitterT (EmitterT go) = liftM (second DL.toList) $ runWriterT go

execEmitterT :: Monad m => EmitterT w m a -> m [w]
execEmitterT = liftM snd . runEmitterT
