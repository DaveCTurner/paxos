{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE LambdaCase #-}

module Network.Paxos.Multi.Acceptor where

import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Writer
import Data.Time
import qualified Data.Map as M
import qualified Data.RangeMap as RM

import Network.Paxos.Multi.Types

data AcceptorState q v = AcceptorState
  { accMinAcceptableProposal      :: RM.RangeMap InstanceId ProposalId
  , accLatestAcceptanceByInstance :: M.Map InstanceId (AcceptedValue q v)
  , accMasterLease                :: Maybe (ProposerId, UTCTime)
  }

-- TODO handling master leases could be outside the core
whenOkProposer :: MonadState (AcceptorState q v) m => UTCTime -> ProposalId -> m () -> m ()
whenOkProposer t p go = do
    isOk <- gets $ checkLease . accMasterLease
    when isOk go
  where
  checkLease Nothing = True
  checkLease (Just (masterPid, expiryTime))
    = t <= expiryTime  &&  masterPid == pidProposerId p

handlePrepare
  :: (MonadWriter [PromisedMessage q v] m, MonadState (AcceptorState q v) m)
  => UTCTime -> PrepareMessage -> m ()
handlePrepare time (Prepare instanceId proposalId MultiPrepare) = whenOkProposer time proposalId $ do

  acceptances <- acceptancesNotBefore instanceId

  let allAcceptancesBefore = case M.maxViewWithKey acceptances of
        Nothing                            -> instanceId
        Just ((maxAcceptedInstance, _), _) -> suc maxAcceptedInstance

  let pidMap = M.unionWith max
        (M.map Just acceptances)
        (M.fromAscList [(i, Nothing) | i <- takeWhile (< allAcceptancesBefore) (iterate suc instanceId)])

  forM_ (M.toList pidMap) $ \(i, maybeAcceptedProposalValue)
    -> tellPromise i proposalId $ maybe Free boundFromAccepted maybeAcceptedProposalValue
  tellPromise allAcceptancesBefore proposalId MultiPromise

handlePrepare time (Prepare instanceId proposalId SinglePrepare) = whenOkProposer time proposalId $ do
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
  => UTCTime -> (ProposedMessage q v) -> m ()
handleProposed time (Proposed instanceId proposalId value) = whenOkProposer time proposalId $ do

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
