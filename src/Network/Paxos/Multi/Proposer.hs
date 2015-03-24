{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE LambdaCase #-}

module Network.Paxos.Multi.Proposer where

import Control.Applicative
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Writer
import Data.Maybe
import qualified Data.Map as M
import qualified Data.Set as S

import Network.Paxos.Multi.Types

data PromisesState q v
  = CollectingPromises
    { cprPromises :: S.Set AcceptorId
    , cprMaxAccepted :: Maybe (AcceptedValue q v)
    }
  | ReadyToPropose
  | ValueProposed

data InstanceProposerState q v = InstanceProposerState
  { iprProposalId      :: ProposalId
  , iprValue           :: Maybe (Value q v)
  , iprPromisesState   :: PromisesState q v
  }

data ProposersState q v = ProposersState
  { pprProposalId          :: ProposalId
  , pprMinMultiInstance    :: InstanceId
  , pprPromises            :: S.Set AcceptorId
  , pprTopology            :: q
  , pprProposersByInstance :: M.Map InstanceId (InstanceProposerState q v)
  }

handleChosen
  :: (MonadState (ProposersState q v) m, MonadWriter [PrepareMessage] m)
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
        , pprPromises            = S.empty
        , pprTopology            = topology
        , pprProposersByInstance = M.map updateInstanceState $ pprProposersByInstance s
        }

      maybeMinInstance <- gets $ fmap (fst . fst) . M.minViewWithKey . pprProposersByInstance
      minMultiInstance <- gets pprMinMultiInstance

      tell [Prepare (fromMaybe minMultiInstance maybeMinInstance) newProposalId MultiPrepare]

spawnInstanceProposersTo :: (Quorum q, MonadState (ProposersState q v) m) => InstanceId -> m ()
spawnInstanceProposersTo newMinMultiInstance = do
  oldMinMultiInstance <- gets pprMinMultiInstance
  forM_ (takeWhile (< newMinMultiInstance) $ iterate suc oldMinMultiInstance) $ \newInstance -> do
    s <- get

    promisesState <- execStateT (checkIfReady $ pprTopology s) CollectingPromises
                        { cprPromises = pprPromises s
                        , cprMaxAccepted = Nothing
                        }

    put $ s
      { pprMinMultiInstance = suc newInstance
      , pprProposersByInstance
          = M.insert newInstance InstanceProposerState
                { iprProposalId      = pprProposalId s
                , iprValue           = Nothing
                , iprPromisesState   = promisesState
                } $ pprProposersByInstance s
      }

handlePromise
  :: (MonadState (ProposersState q v) m, MonadWriter [ProposedMessage q v] m, Quorum q)
  => AcceptorId -> PromisedMessage q v -> m ()
handlePromise acceptorId (Promised instanceId proposalId MultiPromise) = do
  spawnInstanceProposersTo instanceId
  minMultiInstance <- gets pprMinMultiInstance
  forM_ (takeWhile (< minMultiInstance) $ iterate suc instanceId) $ \existingInstance
    -> handlePromise acceptorId (Promised existingInstance proposalId Free)

  multiProposalId <- gets pprProposalId
  when (proposalId == multiProposalId) $ modify $ \s -> s { pprPromises = S.insert acceptorId $ pprPromises s }

handlePromise acceptorId (Promised instanceId proposalId Free) =
  handleIndividualPromise acceptorId instanceId proposalId Nothing

handlePromise acceptorId (Promised instanceId proposalId (Bound previousProposal value)) =
  handleIndividualPromise acceptorId instanceId proposalId (Just $ AcceptedValue previousProposal value)

handleIndividualPromise
  :: (MonadState (ProposersState q v) m, MonadWriter [ProposedMessage q v] m, Quorum q)
  => AcceptorId -> InstanceId -> ProposalId -> Maybe (AcceptedValue q v) -> m ()
handleIndividualPromise acceptorId instanceId proposalId maybeAcceptedValue = do
  spawnInstanceProposersTo $ suc instanceId
  let mkProposedMessage = Proposed instanceId proposalId
  topology <- gets pprTopology
  maybeInstanceProposerState <- gets $ M.lookup instanceId . pprProposersByInstance
  case maybeInstanceProposerState of

    Nothing -> return () -- Instance is obsolete

    Just ipr -> when (iprProposalId ipr == proposalId) $ do

      newPromisesState <- flip execStateT (iprPromisesState ipr) $ do
        insertPromise acceptorId maybeAcceptedValue
        maybeValueToPropose <- checkIfReady topology
        proposeIfReady mkProposedMessage
          $ fmap valueFromAccepted maybeValueToPropose <|> iprValue ipr

      -- TODO must ensure that pidTopologyVersion proposalId <= instanceTopologyVersion

      modify $ \s -> s
        { pprProposersByInstance = M.insert instanceId ipr
            { iprPromisesState = newPromisesState }
            $ pprProposersByInstance s
        }

insertPromise :: MonadState (PromisesState q v) m => AcceptorId -> Maybe (AcceptedValue q v) -> m ()
insertPromise acceptorId maybeAcceptedValue = get >>= \case
  CollectingPromises{..} -> put $ CollectingPromises
    { cprPromises = S.insert acceptorId cprPromises
    , cprMaxAccepted = max maybeAcceptedValue cprMaxAccepted
    }
  _ -> return ()

checkIfReady :: (Quorum q, MonadState (PromisesState q v) m)
  => q -> m (Maybe (AcceptedValue q v))
checkIfReady q = get >>= \case
  CollectingPromises{..}
    | isQuorum q cprPromises -> do
          put ReadyToPropose
          return cprMaxAccepted
  _ -> return Nothing

proposeIfReady
  :: (MonadState (PromisesState q v) m, MonadWriter [ProposedMessage q v] m)
  => (Value q v -> ProposedMessage q v) -> Maybe (Value q v) -> m ()
proposeIfReady mkProposedMessage (Just value) = get >>= \case
  ReadyToPropose -> do
        tell [mkProposedMessage value]
        put ValueProposed
  _ -> return ()
proposeIfReady _ _ = return ()
