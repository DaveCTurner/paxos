{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE LambdaCase #-}

module Network.Paxos.Multi.Acceptor where

import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Writer
import qualified Data.Map as M
import qualified Data.RangeMap as RM

import Network.Paxos.Multi.Types

data AcceptorState q v = AcceptorState
  { accMinAcceptableProposal      :: RM.RangeMap InstanceId ProposalId
  , accLatestAcceptanceByInstance :: M.Map InstanceId (AcceptedValue q v)
  }

handlePrepare
  :: (MonadWriter [PromisedMessage q v] m, MonadState (AcceptorState q v) m)
  => PrepareMessage -> m ()
handlePrepare (Prepare instanceId proposalId MultiPrepare) = do

  acceptances <- acceptancesNotBefore instanceId

  let instanceGreaterThanAllAcceptances = case M.maxViewWithKey acceptances of
        Nothing                            -> instanceId
        Just ((maxAcceptedInstance, _), _) -> suc maxAcceptedInstance

  let pidMap = M.unionWith max
        (M.map Just acceptances)
        (M.fromAscList
          [(i, Nothing) | i <- takeWhile (< instanceGreaterThanAllAcceptances) (iterate suc instanceId)])

  forM_ (M.toList pidMap) $ \(i, maybeAcceptedProposalValue)
    -> tellPromise i proposalId $ maybe Free boundFromAccepted maybeAcceptedProposalValue

  tellPromise instanceGreaterThanAllAcceptances proposalId MultiPromise

handlePrepare (Prepare instanceId proposalId SinglePrepare) = do
  maybeCurrentAcceptance <- gets $ M.lookup instanceId . accLatestAcceptanceByInstance
  tellPromise instanceId proposalId $ maybe Free boundFromAccepted maybeCurrentAcceptance

acceptancesNotBefore :: MonadState (AcceptorState q v) m
  => InstanceId -> m (M.Map InstanceId (AcceptedValue q v))
acceptancesNotBefore instanceId = do
  (_, maybeCurrentAcceptance, futureAcceptances)
    <- gets $ M.splitLookup instanceId . accLatestAcceptanceByInstance
  return $ maybe id (M.insert instanceId) maybeCurrentAcceptance
         $ futureAcceptances

handleProposed
  :: (MonadWriter [AcceptedMessage q v] m, MonadState (AcceptorState q v) m)
  => (ProposedMessage q v) -> m ()
handleProposed (Proposed instanceId proposalId value) = do

  maybeMinAcceptableProposal <- gets $ RM.lookup instanceId . accMinAcceptableProposal

  let isAcceptable = case maybeMinAcceptableProposal of
          Nothing -> True
          Just minAcceptableProposal -> minAcceptableProposal <= proposalId

  when isAcceptable $ tellAccept instanceId proposalId value

tellPromise
  :: (MonadWriter [PromisedMessage q v] m, MonadState (AcceptorState q v) m)
  => InstanceId -> ProposalId -> (PromiseType q v) -> m ()
tellPromise i p t = do
  let msg = Promised i p t
  tell [msg]
  let promiseRange = case t of
        MultiPromise -> RM.inclusiveUnbounded i
        _     -> RM.inclusiveInclusive i i
  modify $ \s -> s { accMinAcceptableProposal = RM.insertWith max promiseRange p $ accMinAcceptableProposal s }

tellAccept
  :: (MonadWriter [AcceptedMessage q v] m, MonadState (AcceptorState q v) m)
  => InstanceId -> ProposalId -> Value q v -> m ()
tellAccept i p v = do
  tell [Accepted i p v]
  modify $ \s -> s { accLatestAcceptanceByInstance
      = M.insertWith max i (AcceptedValue p v) $ accLatestAcceptanceByInstance s }
