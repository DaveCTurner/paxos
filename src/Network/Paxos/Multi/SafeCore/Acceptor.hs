{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE LambdaCase #-}

{-| Implementation of a single acceptor. A quorum of acceptors is required to
choose a value. 

Acceptors satisfy the following invariants:

- May send @'Promised' instanceId proposalId 'MultiPromise'@ as long as it has not
  previously sent @'Accepted' instanceId' proposalId' value'@ for any
  @instanceId' >= instanceId@ and any @proposalId'@ and @value'@.

- May send @'Promised' instanceId proposalId 'Free'@ as long as it has not
  previously sent @'Accepted' instanceId proposalId' value'@ for any
  @proposalId'@ and @value'@.

- May send @'Promised' instanceId proposalId ('Bound' proposalId' value')@ as long
  as @proposalId' < proposalId@, it has previously sent @'Accepted' instanceId
  proposalId' value'@, and it has not previously sent @'Accepted' instanceId
  proposalId'' value''@ for any @proposalId'' > proposalId'@.

- May send @'Accepted' instanceId proposalId value@ as long as it has received
  @'Proposed' instanceId proposalId value@, and has not previously sent
  @'Promised' instanceId proposalId' promiseType@ for any @proposalId' >
  proposalId@ and any @promiseType@.

-}

module Network.Paxos.Multi.SafeCore.Acceptor
  ( AcceptorState
  , initialAcceptorState
  , handlePrepare
  , handleProposed
  , archiveUpToInstance
  ) where

import Control.Monad.Reader
import Control.Monad.State
import qualified Data.Map as M
import qualified Data.RangeMap as RM

import Network.Paxos.Multi.Types

{-| The state of an individual acceptor. -}
data AcceptorState q v = AcceptorState
  { accMinActiveInstance          :: InstanceId
  {- ^ Tracks the minimum @instanceId@ for which any @'Promised' instanceId _
_@ or @'Accepted' instanceId _ _@ may be sent. State for instances prior to
@accMinActiveInstance@ can be discarded. -}

  , accMinAcceptableProposal      :: RM.RangeMap InstanceId ProposalId
  {- ^ For each @instanceId > accMinActiveInstance@, records the maximum
@proposalId@ for which a @'Promised' instanceId proposalId _@ has been sent
which is therefore the minimum @proposalId@ for which an @'Accepted' instanceId
proposalId _@ may be sent. -}

  , accLatestAcceptanceByInstance :: M.Map InstanceId (AcceptedValue q v)
  {- ^ For each @instanceId > accMinActiveInstance@, records the maximum
@proposalId@ and corresponding @value@ for which an @'Accepted' instanceId
proposalId value@ has been sent.  If there is no entry for @instanceId@ then no
'Accepted' message has been sent for that instance. In particular, this
includes all instances greater than the maximum 'instanceId' in this map. -}
  }

{-| The initial state of an individual acceptor, before it has processed any messages. -}
initialAcceptorState :: AcceptorState q v
initialAcceptorState = AcceptorState
  { accMinAcceptableProposal      = RM.empty
  , accLatestAcceptanceByInstance = M.empty
  , accMinActiveInstance          = InstanceId 0
  }

whenActive :: MonadState (AcceptorState q v) m => InstanceId -> m () -> m ()
whenActive instanceId go = do
  minActiveInstance <- gets accMinActiveInstance
  when (minActiveInstance <= instanceId) go

{-| Handle a 'PrepareMessage', which may result in some 'PromisedMessage'
outputs that should be sent to the proposer that originally sent the
'PrepareMessage'. -}
handlePrepare
  :: (MonadEmitter m, Emitted m ~ PromisedMessage q v, MonadState (AcceptorState q v) m)
  => PrepareMessage -> m ()
handlePrepare (Prepare givenInstanceId proposalId MultiPrepare) = do

  instanceId <- gets $ max givenInstanceId . accMinActiveInstance

  acceptances <- acceptancesNotBefore instanceId

  let instanceGreaterThanAllAcceptances = case M.maxViewWithKey acceptances of
        Nothing                            -> instanceId
        Just ((maxAcceptedInstance, _), _) -> suc maxAcceptedInstance

  let pidMap = M.unionWith max
        (M.map Just acceptances)
        (M.fromAscList
          [(i, Nothing) | i <- takeWhile (< instanceGreaterThanAllAcceptances) (iterate suc instanceId)])

  forM_ (M.toList pidMap) $ \(i, maybeAcceptedProposalValue) -> case maybeAcceptedProposalValue of
    Nothing -> tellPromise i proposalId Free
    Just (AcceptedValue acceptedProposal value) -> when (acceptedProposal < proposalId)
      $ tellPromise i proposalId $ Bound acceptedProposal value

  tellPromise instanceGreaterThanAllAcceptances proposalId MultiPromise

handlePrepare (Prepare instanceId proposalId SinglePrepare) = whenActive instanceId $ do
  maybeCurrentAcceptance <- gets $ M.lookup instanceId . accLatestAcceptanceByInstance
  case maybeCurrentAcceptance of
    Nothing -> tellPromise instanceId proposalId Free
    Just (AcceptedValue acceptedProposal value) -> when (acceptedProposal < proposalId)
      $ tellPromise instanceId proposalId $ Bound acceptedProposal value

acceptancesNotBefore :: MonadState (AcceptorState q v) m
  => InstanceId -> m (M.Map InstanceId (AcceptedValue q v))
acceptancesNotBefore instanceId = do
  (_, maybeCurrentAcceptance, futureAcceptances)
    <- gets $ M.splitLookup instanceId . accLatestAcceptanceByInstance
  return $ maybe id (M.insert instanceId) maybeCurrentAcceptance futureAcceptances

{-| Handle a 'ProposedMessage', which may result in an 'AcceptedMessage' output
that should be broadcast to all learners. -}
handleProposed
  :: (MonadEmitter m, Emitted m ~ AcceptedMessage q v, MonadState (AcceptorState q v) m)
  => ProposedMessage q v -> m ()
handleProposed (Proposed instanceId proposalId value) = whenActive instanceId $ do

  maybeMinAcceptableProposal <- gets $ RM.lookup instanceId . accMinAcceptableProposal

  let isAcceptable = case maybeMinAcceptableProposal of
          Nothing -> True
          Just minAcceptableProposal -> minAcceptableProposal <= proposalId

  when isAcceptable $ tellAccept instanceId proposalId value

tellPromise
  :: (MonadEmitter m, Emitted m ~ PromisedMessage q v, MonadState (AcceptorState q v) m)
  => InstanceId -> ProposalId -> PromiseType q v -> m ()
tellPromise i p t = do
  emit $ Promised i p t
  let promiseRange = case t of
        MultiPromise -> RM.inclusiveUnbounded i
        _            -> RM.inclusiveInclusive i i
  modify $ \s -> s { accMinAcceptableProposal = RM.insertWith max promiseRange p $ accMinAcceptableProposal s }

tellAccept
  :: (MonadEmitter m, Emitted m ~ AcceptedMessage q v, MonadState (AcceptorState q v) m)
  => InstanceId -> ProposalId -> Value q v -> m ()
tellAccept i p v = do
  emit $ Accepted i p v
  modify $ \s -> s { accLatestAcceptanceByInstance
      = M.insertWith max i (AcceptedValue p v) $ accLatestAcceptanceByInstance s }

{-| Clear out state pertaining to instances that have been chosen and whose
results are /reliably/ stored elsewhere. This means that any learner that has
not learned all the values chosen in instances @<= instanceId@ will be unable
to proceed without restarting or looking elsewhere for chosen values. -}
archiveUpToInstance :: MonadState (AcceptorState q v) m => InstanceId -> m ()
archiveUpToInstance instanceId  = modify $ \s -> s  
  { accMinAcceptableProposal = RM.delete (RM.unboundedInclusive instanceId)
        $ accMinAcceptableProposal s
  , accLatestAcceptanceByInstance = snd $ M.split instanceId
        $ accLatestAcceptanceByInstance s
  , accMinActiveInstance = max (suc instanceId) (accMinActiveInstance s)
  }
