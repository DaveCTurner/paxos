{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE LambdaCase #-}

{-| Implementation of a single acceptor. A quorum of acceptors is required to
choose a value. -}

module Network.Paxos.Multi.Acceptor
  ( AcceptorState
  , initialAcceptorState
  , handlePrepare
  , handleProposed
  , archiveUpToInstance
  ) where

import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Writer
import qualified Data.Map as M
import qualified Data.RangeMap as RM

import Network.Paxos.Multi.Types

{- Acceptor invariants:

May send [Promise instanceId proposalId Free] as long as nothing has been
accepted for instance instanceId

May send [Promise instanceId proposalId MultiPromise] as long as nothing has
been accepted for any instance >= instanceId

May send [Promise instanceId proposalId (Bound p v)] as long as p is the
greatest proposal accepted so far for instance instanceId, where v =
value_accepted instanceId p is the value of the proposal that was accepted at p
and is equal to value_promised instanceId proposalId

May not update value_promised after a bound promise has been sent
(so that two promises for the same proposal must have the same PromiseType).

May send [Accepted instanceId proposalId value] if:
  - Proposed instanceId proposalId value is received
  - value_accepted instanceId proposalId = value_proposed instanceId proposalId
  - proposalId is at least equal to the minimum acceptable proposal
       (according to the various promises already sent)

May not update value_accepted instanceId proposalId after sending
[Accepted instanceId proposalId value]

-}

{-| The state of an individual acceptor. -}
data AcceptorState q v = AcceptorState
  { accMinAcceptableProposal      :: RM.RangeMap InstanceId ProposalId
  , accLatestAcceptanceByInstance :: M.Map InstanceId (AcceptedValue q v)
  }

{-| The initial state of an individual acceptor, before it has processed any messages. -}
initialAcceptorState :: AcceptorState q v
initialAcceptorState = AcceptorState
  { accMinAcceptableProposal      = RM.empty
  , accLatestAcceptanceByInstance = M.empty
  }

{-| Handle a 'PrepareMessage', which may result in some 'PromisedMessage'
outputs that should be sent to the proposer that originally sent the
'PrepareMessage'. -}
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

{-| Handle a 'ProposedMessage', which may result in an 'AcceptedMessage' output
that should be broadcast to all learners. -}
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

{-| Clear out state pertaining to instances that have been chosen and whose
results are /reliably/ stored elsewhere. After calling @archiveUpToInstance
instanceId@, the acceptor /must/ receive no further messages that relate to
instances @<= instanceId@. This means that any learner that has not learned all
the values chosen in instances @<= instanceId@ will be unable to proceed
without restarting. -}
archiveUpToInstance :: MonadState (AcceptorState q v) m => InstanceId -> m ()
archiveUpToInstance instanceId  = modify $ \s -> s  
  { accMinAcceptableProposal = RM.delete (RM.unboundedInclusive instanceId)
        $ accMinAcceptableProposal s
  , accLatestAcceptanceByInstance = snd $ M.split instanceId
        $ accLatestAcceptanceByInstance s
  }
