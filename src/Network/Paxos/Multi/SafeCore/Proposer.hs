{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-| Implementation of a single proposer, which collects @'Promised' instanceId
proposalId promiseType@ messags until it has a quorum. It therefore has to keep
track of the cluster topology (which defines what \'quorum\' means). It is
acceptable for the known topology to be slightly out of date, of course.

Let @firstUnchosenInstance@ be the lowest-numbered instance that the proposer
thinks has not been chosen. Then a proposer may send a @'Proposed' instanceId
proposalId value@ message as long as

- @instanceId >= firstUnchosenInstance@,

- @'pidTopologyVersion' proposalId@ is no greater than the topology version of
  @firstUnchosenInstance@,

- there is a set 'S' of acceptors from which it has received @'Promised'
  instanceId proposalId _@ messages, and

- 'S' is a quorum according to the topology with version @'pidTopologyVersion'
  proposalId@.

- If any of the 'Promised' messages received from the acceptors in 'S' are of
  the form @'Promised' instanceId proposalId (Bound proposalId' value')@ then
  @value@ must be equal to the @value'@ corresponding to the maximum such
  @proposalId'@.

The proposer works on at most one @proposalId@ for each instance at any one
time. If it receives a 'Promised' message for a later-numbered proposal with
the same 'pidProposerId' then it considers the current @proposalId@ to be
abandoned and start work on the new one.

It cannot, however, work on a proposal with @'pidTopologyVersion' proposalId@
greater than the topology version of @firstUnchosenInstance@. In practice, no
such proposals should ever be generated.

'MultiPromise' messages affect infinitely many instances simultaneously. All
but finitely many such affected instances will be in identical states, so are
combined together. The 'spawnNextInstance' action is used to split the
lowest-numbered instance out from the infinite set and assign it a value.

-}

module Network.Paxos.Multi.SafeCore.Proposer
  ( ProposerState
  , initialProposerState
  , joiningProposerState
  , handlePromise
  , spawnNextInstance
  , handleChosen
  ) where

import Control.Monad.Reader
import Control.Monad.State
import qualified Data.Map as M
import qualified Data.Set as S

import Network.Paxos.Multi.Types

data PromisesState q v
  = CollectingPromises
    { cprPromises :: S.Set AcceptorId
    , cprMaxAccepted :: Maybe (AcceptedValue q v)
    }
  | ValueProposed

data MultiPromisesState
  = CollectingMultiPromises (S.Set AcceptorId)
  | ReadyToPropose

data InstanceProposerState q v = InstanceProposerState
  { iprProposalId      :: ProposalId
  , iprValue           :: Value q v
  , iprPromisesState   :: PromisesState q v
  }

{-| The state of a proposer. -}
data ProposerState q v = ProposerState
  { pprMinMultiInstance                 :: InstanceId
  , pprMultiProposalId                  :: ProposalId
  , pprMultiPromises                    :: MultiPromisesState
  , pprTopology                         :: TopologyHistory q
  , pprProposersByInstance              :: M.Map InstanceId (InstanceProposerState q v)
  }

{-| The initial state of a proposer. If the proposer is joining a cluster that
has been running for some time, use 'joiningProposerState'. -}
initialProposerState :: Quorum q => ProposerId -> q -> ProposerState q v
initialProposerState pid topology
  = joiningProposerState pid (InstanceId 0) $ initialTopology topology

{-| The initial state of a proposer joining a running cluster. -}
joiningProposerState
  :: Quorum q
  => ProposerId
  -> InstanceId -- ^ The first unchosen instance.
  -> TopologyHistory q -- ^ The current and previous topologies at the first unchosen instance.
  -> ProposerState q v
joiningProposerState pid instanceId topology = ProposerState
  { pprMinMultiInstance                 = instanceId
  , pprMultiProposalId                  = ProposalId
      { pidTopologyVersion = topoVersion topology
      , pidProposal        = ProposalNumber 0
      , pidProposerId      = pid
      }
  , pprMultiPromises                    = CollectingMultiPromises S.empty
  , pprTopology                         = topology
  , pprProposersByInstance              = M.empty
  }

{-| Record that the given instance was chosen with the given value: discard the
in-progress proposal states and update the topology as appropriate. -}
handleChosen :: (Quorum q, MonadState (ProposerState q v) m) => InstanceId -> Value q v -> m ()
handleChosen instanceId value = do
  modify $ \s -> s { pprTopology = pushTopology value $ pprTopology s }

  minMultiInstance <- gets pprMinMultiInstance
  modify $ \s -> if minMultiInstance <= instanceId
    then s { pprMinMultiInstance = suc instanceId
           , pprProposersByInstance = M.empty }
    else s { pprProposersByInstance = snd $ M.split instanceId $ pprProposersByInstance s }

spawnInstanceProposersTo
  :: (MonadState (ProposerState q v) m, MonadEmitter m, Emitted m ~ ProposedMessage q v)
  => InstanceId -> m ()
spawnInstanceProposersTo newMinMultiInstance = go
  where
  go = do
    oldMinMultiInstance <- gets pprMinMultiInstance
    when (oldMinMultiInstance < newMinMultiInstance)
      $ spawnNextInstance NoOp >> go

{-| Spawn the next available instance with the given value. If enough promises have already
been received, results in a 'ProposedMessage' which should be broadcast to all acceptors. -}
spawnNextInstance
  :: (MonadState (ProposerState q v) m, MonadEmitter m, Emitted m ~ ProposedMessage q v)
  => Value q v -> m InstanceId
spawnNextInstance value = do
  newInstance      <- gets pprMinMultiInstance
  multiPromises    <- gets pprMultiPromises
  proposalId       <- gets pprMultiProposalId

  promisesState <- case multiPromises of
    ReadyToPropose -> do
      emit $ Proposed newInstance proposalId value
      return ValueProposed

    CollectingMultiPromises promises -> return CollectingPromises
      { cprPromises = promises, cprMaxAccepted = Nothing }

  modify $ \s -> s
    { pprMinMultiInstance = suc newInstance
    , pprProposersByInstance
        = M.insert newInstance InstanceProposerState
              { iprProposalId      = proposalId
              , iprValue           = value
              , iprPromisesState   = promisesState
              } $ pprProposersByInstance s
    }

  return newInstance

{-| Handle a 'PromisedMessage' indicating a commitment from an acceptor not to
accept any earlier-numbered proposals. May result in some 'ProposedMessage'
outputs which should be broadcast to all acceptors. -}
handlePromise
  :: (MonadState (ProposerState q v) m, MonadEmitter m, Emitted m ~ ProposedMessage q v, Quorum q)
  => AcceptorId -> PromisedMessage q v -> m ()

handlePromise acceptorId (Promised instanceId proposalId MultiPromise) = do
  spawnInstanceProposersTo instanceId
  minMultiInstance <- gets pprMinMultiInstance
  forM_ (takeWhile (< minMultiInstance) $ iterate suc instanceId) $ \existingInstance
    -> handlePromise acceptorId (Promised existingInstance proposalId Free)

  bumpMultiProposalId proposalId

  multiProposalId <- gets pprMultiProposalId
  when (proposalId == multiProposalId) $ do
    maybeTopology <- gets $ getTopology proposalId . pprTopology
    multiPromises <- gets pprMultiPromises

    case (maybeTopology, multiPromises) of
      (Just topology, CollectingMultiPromises promises) -> do
        let promises' = S.insert acceptorId promises
        modify $ \s -> s
          { pprMultiPromises
              = if isQuorum topology promises'
                then ReadyToPropose
                else CollectingMultiPromises promises'
          }
      _ -> return ()

handlePromise acceptorId (Promised instanceId proposalId Free) =
  handleIndividualPromise acceptorId instanceId proposalId Nothing

handlePromise acceptorId (Promised instanceId proposalId (Bound previousProposal value)) =
  handleIndividualPromise acceptorId instanceId proposalId (Just $ AcceptedValue previousProposal value)

bumpMultiProposalId :: MonadState (ProposerState q v) m => ProposalId -> m ()
bumpMultiProposalId newMultiProposalId = do
  oldMultiProposalId <- gets pprMultiProposalId
  when (oldMultiProposalId     <       newMultiProposalId
     && oldMultiProposalId `canBumpTo` newMultiProposalId)
    $ modify $ \s -> s
      { pprMultiProposalId = newMultiProposalId
      , pprMultiPromises = CollectingMultiPromises S.empty
      }

canBumpTo :: ProposalId -> ProposalId -> Bool
canBumpTo p1 p2 = pidTopologyVersion p1 == pidTopologyVersion p2
               && pidProposerId      p1 == pidProposerId      p2

handleIndividualPromise
  :: (MonadState (ProposerState q v) m, MonadEmitter m, Emitted m ~ ProposedMessage q v, Quorum q)
  => AcceptorId -> InstanceId -> ProposalId -> Maybe (AcceptedValue q v) -> m ()
handleIndividualPromise acceptorId instanceId proposalId maybeAcceptedValue = do
  spawnInstanceProposersTo $ suc instanceId
  maybeInstanceProposerState <- gets $ M.lookup instanceId . pprProposersByInstance
  case maybeInstanceProposerState of

    Nothing -> return () -- Instance is obsolete

    Just ipr -> case compare (iprProposalId ipr) proposalId of
      LT ->
        -- Promise is for a higher-numbered proposal, but with the same topology.
        -- This means that the current proposal has been abandoned. Start again
        -- with the new proposal.
        when (iprProposalId ipr `canBumpTo` proposalId)
          $ collectPromise ipr
              { iprProposalId    = proposalId
              , iprPromisesState = CollectingPromises
                  { cprPromises = S.empty, cprMaxAccepted = Nothing }
              }

      EQ -> -- Promise is for the current proposal, which needs more promises.
        collectPromise ipr

      GT -> -- Promise is for an obsolete proposal - ignore it.
        return ()

  where
  collectPromise ipr@(InstanceProposerState {iprPromisesState = CollectingPromises{..}}) = do
    let cprPromises'    = S.insert acceptorId cprPromises
        cprMaxAccepted' = max maybeAcceptedValue cprMaxAccepted

    maybeTopology <- gets $ getTopology proposalId . pprTopology

    newPromisesState <- case maybeTopology of
      Just topology
        | isQuorum topology cprPromises' -> do
            emit $ Proposed instanceId proposalId $ maybe (iprValue ipr) valueFromAccepted cprMaxAccepted'
            return ValueProposed

      _ -> return CollectingPromises { cprPromises = cprPromises', cprMaxAccepted = cprMaxAccepted' }

    modify $ \s -> s
      { pprProposersByInstance = M.insert instanceId ipr
          { iprPromisesState = newPromisesState }
          $ pprProposersByInstance s
      }

  collectPromise _ = return ()
