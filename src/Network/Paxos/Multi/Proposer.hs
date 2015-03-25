{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-| Implementation of a single proposer, which collects each 'PromisedMessage'
until it has a quorum. -}

-- TODO NACKs should bump the proposal id

module Network.Paxos.Multi.Proposer
  ( ProposerState
  , initialProposerState
  , handleChosen
  , handlePromise
  ) where

import Control.Monad.Reader
import Control.Monad.State
import Data.Maybe
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
  { pprProposalId          :: ProposalId
  , pprMinMultiInstance    :: InstanceId
  , pprPromises            :: MultiPromisesState
  , pprTopology            :: q
  , pprProposersByInstance :: M.Map InstanceId (InstanceProposerState q v)
  }

{-| The initial state of a proposer. If the proposer is joining a cluster that has
been running for some time, use 'handleChosen' to bring it up to date with the last
chosen instance. -}
initialProposerState :: ProposerId -> q -> ProposerState q v
initialProposerState pid topology = ProposerState
  { pprProposalId          = ProposalId
      { pidTopologyVersion = TopologyVersion 0
      , pidProposal        = ProposalNumber 0
      , pidProposerId      = pid
      }
  , pprMinMultiInstance    = InstanceId 0
  , pprPromises            = CollectingMultiPromises S.empty
  , pprTopology            = topology
  , pprProposersByInstance = M.empty
  }

{-| Handle the event that a new value has been chosen, which removes data about
preceding instances and may also update the topology. -}
handleChosen
  :: (MonadState (ProposerState q v) m, MonadEmitter m, Emitted m ~ PrepareMessage)
  => InstanceId -> TopologyVersion -> q -> m ()
handleChosen instanceId topologyVersion topology = removeChosenInstances >> bumpProposalTopologies
  where
  
  removeChosenInstances = do
    minMultiInstance <- gets pprMinMultiInstance
    modify $ \s -> if minMultiInstance <= instanceId
      then s { pprMinMultiInstance = suc instanceId
             , pprProposersByInstance = M.empty }
      else s { pprProposersByInstance = snd $ M.split instanceId $ pprProposersByInstance s }

  bumpProposalTopologies = do
    oldProposalId <- gets pprProposalId
    let newProposalId = oldProposalId
                            { pidTopologyVersion = topologyVersion
                            , pidProposal        = ProposalNumber 0
                            }
    when (oldProposalId < newProposalId) $ do

      let updateInstanceState ipr = ipr
              { iprProposalId    = newProposalId
              , iprPromisesState = CollectingPromises
                  { cprPromises    = S.empty
                  , cprMaxAccepted = Nothing
                  }
              }

      modify $ \s -> s
        { pprProposalId          = newProposalId
        , pprPromises            = CollectingMultiPromises S.empty
        , pprTopology            = topology
        , pprProposersByInstance = M.map updateInstanceState $ pprProposersByInstance s
        }

      maybeMinInstance <- gets $ fmap (fst . fst) . M.minViewWithKey . pprProposersByInstance
      minMultiInstance <- gets pprMinMultiInstance

      emit $ Prepare (fromMaybe minMultiInstance maybeMinInstance) newProposalId MultiPrepare

spawnInstanceProposersTo
  :: (MonadState (ProposerState q v) m, MonadEmitter m, Emitted m ~ ProposedMessage q v)
  => InstanceId -> m ()
spawnInstanceProposersTo newMinMultiInstance = go
  where
  go = do
    oldMinMultiInstance <- gets pprMinMultiInstance
    when (oldMinMultiInstance < newMinMultiInstance) $ do
      spawnNextInstance NoOp
      go

{-| Spawn the next available instance with the given value. If enough promises have already
been received, results in a 'ProposedMessage' which should be broadcast to all acceptors. -}
spawnNextInstance
  :: (MonadState (ProposerState q v) m, MonadEmitter m, Emitted m ~ ProposedMessage q v)
  => Value q v -> m ()
spawnNextInstance value = do
  newInstance      <- gets pprMinMultiInstance
  multiPromises    <- gets pprPromises
  proposalId       <- gets pprProposalId

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

  multiProposalId <- gets pprProposalId
  when (proposalId == multiProposalId) $ gets pprPromises >>= \case
    CollectingMultiPromises promises -> do
      let promises' = S.insert acceptorId promises 
      topology <- gets pprTopology
      modify $ \s -> s
        { pprPromises
            = if isQuorum topology promises'
              then ReadyToPropose
              else CollectingMultiPromises promises'
        }
    _ -> return ()

handlePromise acceptorId (Promised instanceId proposalId Free) =
  handleIndividualPromise acceptorId instanceId proposalId Nothing

handlePromise acceptorId (Promised instanceId proposalId (Bound previousProposal value)) =
  handleIndividualPromise acceptorId instanceId proposalId (Just $ AcceptedValue previousProposal value)

handleIndividualPromise
  :: (MonadState (ProposerState q v) m, MonadEmitter m, Emitted m ~ ProposedMessage q v, Quorum q)
  => AcceptorId -> InstanceId -> ProposalId -> Maybe (AcceptedValue q v) -> m ()
handleIndividualPromise acceptorId instanceId proposalId maybeAcceptedValue = do
  spawnInstanceProposersTo $ suc instanceId
  topology <- gets pprTopology
  maybeInstanceProposerState <- gets $ M.lookup instanceId . pprProposersByInstance
  case maybeInstanceProposerState of

    Nothing -> return () -- Instance is obsolete

    Just ipr -> when (iprProposalId ipr == proposalId) $ case (iprPromisesState ipr) of
      CollectingPromises{..} -> do

        let cprPromises'    = S.insert acceptorId cprPromises
            cprMaxAccepted' = max maybeAcceptedValue cprMaxAccepted

        newPromisesState <- if isQuorum topology cprPromises'
          then do
            emit $ Proposed instanceId proposalId $ maybe (iprValue ipr) valueFromAccepted cprMaxAccepted'
            return ValueProposed
          else return CollectingPromises { cprPromises = cprPromises', cprMaxAccepted = cprMaxAccepted' }

        modify $ \s -> s
          { pprProposersByInstance = M.insert instanceId ipr
              { iprPromisesState = newPromisesState }
              $ pprProposersByInstance s
          }

      _ -> return ()
