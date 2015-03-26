{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE LambdaCase #-}

{-| Implementation of a learner, which collects each 'AcceptedMessage' it
receives until it has a quorum.

A learner may send a @'Chosen' instanceId value@ message when there is a @proposalId@ such that:

- the topology version of @instanceId@ is at most @'pidTopologyVersion'
  proposalId + 1@ (so that the proposal is not too out-of-date).

- there is a nonempty set 'S' of acceptors from which it has received
  @'Accepted' instanceId proposalId _@.

- 'S' is a quorum according to the topology with version @'pidTopologyVersion'
  proposalId@.

- the learner has previously sent a 'Chosen' message for the instance before
  @instanceId@ (or @instanceId == 'InstanceId' 0@).

In this case @value@ may be the value of any of the 'Accepted' messages
received: they will all be equal because of the invariants elsewhere in the
system.

-}

module Network.Paxos.Multi.SafeCore.Learner
  ( LearnerState
  , initialLearnerState
  , joiningLearnerState
  , handleAccepted
  ) where

import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Trans.Maybe
import Data.Void
import qualified Data.Map as M
import qualified Data.Set as S

import Network.Paxos.Multi.Types

data Acceptances q v = Acceptances
  { accSet :: S.Set AcceptorId
  , accValue :: Value q v
  }

combineAcceptances :: Acceptances q v -> Acceptances q v -> Acceptances q v
combineAcceptances Acceptances{accSet=set1, accValue=v1} Acceptances{accSet=set2} = Acceptances
  { accSet = S.union set1 set2
{- Only ever combine acceptances for the same instance/proposal, for which the
accepted values are always equal. -}
  , accValue = v1
  }

{-| The state of an individual learner. -}
data LearnerState q v = LearnerState
  { lnrAcceptances                             :: M.Map InstanceId (M.Map ProposalId (Acceptances q v))
  , lnrFirstUnchosenInstance                   :: InstanceId
  , lnrFirstUnchosenTopology                   :: TopologyHistory q
  }

{-| The initial state of an individual learner, before it has processed any
messages and before any values have been chosen. -}
initialLearnerState :: Quorum q => q -> LearnerState q v
initialLearnerState topology = joiningLearnerState (InstanceId 0) $ initialTopology topology

{-| The starting state of a learner which joins the cluster after it has been
running for a while, so the initial sequence of values has been chosen. It only
needs to know at what instance to start working from and the current and
previous topologies.  -}
joiningLearnerState :: InstanceId -> TopologyHistory q -> LearnerState q v
joiningLearnerState instanceId topology = LearnerState
  { lnrAcceptances                             = M.empty
  , lnrFirstUnchosenInstance                   = instanceId
  , lnrFirstUnchosenTopology                   = topology
  }

{-| Handle an 'AcceptedMessage', which may result in one or more
'ChosenMessage' outputs indicating that values were chosen. -}
handleAccepted
  :: (MonadEmitter m, Emitted m ~ ChosenMessage q v, MonadState (LearnerState q v) m, Quorum q)
  => AcceptorId -> AcceptedMessage q v -> m ()
handleAccepted acceptorId (Accepted instanceId proposalId value) = do

  oldFirstUnchosenInstance <- gets lnrFirstUnchosenInstance
  oldFirstUnchosenTopologyVersion <- gets $ topoVersion . lnrFirstUnchosenTopology

  when (instanceId >= oldFirstUnchosenInstance
      && oldFirstUnchosenTopologyVersion <= suc (pidTopologyVersion proposalId)) $ do

    modify $ \s -> s
      { lnrAcceptances = M.insertWith
          (M.unionWith combineAcceptances)
          instanceId
          (M.singleton proposalId $ Acceptances
              { accSet = S.singleton acceptorId
              , accValue = value
              })
          (lnrAcceptances s)
      }

    when (instanceId == oldFirstUnchosenInstance) $ do
      runVoidMaybeT chooseQuorateValues
      newFirstUnchosenInstance <- gets lnrFirstUnchosenInstance
      newFirstUnchosenTopologyVersion <- gets $ topoVersion . lnrFirstUnchosenTopology
      when (oldFirstUnchosenInstance < newFirstUnchosenInstance) $ do

        let removeOldTopologies = M.filterWithKey
              (\pid _ -> newFirstUnchosenTopologyVersion <= suc (pidTopologyVersion pid))

            removeChosenInstances = removeKeysLessThan newFirstUnchosenInstance

        modify $ \s -> s
          { lnrAcceptances = M.map removeOldTopologies $ removeChosenInstances $ lnrAcceptances s
          }

removeKeysLessThan :: InstanceId -> M.Map InstanceId a -> M.Map InstanceId a
removeKeysLessThan instanceId m = case M.splitLookup instanceId m of
  (_, Nothing, m') -> m'
  (_, Just a, m')  -> M.insert instanceId a m'

runVoidMaybeT :: Monad m => MaybeT m Void -> m ()
runVoidMaybeT go = do { _ <- runMaybeT go; return () }

exitLearner :: Monad m => MaybeT m a
exitLearner = mzero

unJust :: Monad m => m (Maybe a) -> MaybeT m a
unJust mma = lift mma >>= \case
  Nothing -> exitLearner
  Just a -> return a

chooseQuorateValues :: (Quorum q, MonadEmitter m, Emitted m ~ ChosenMessage q v, MonadState (LearnerState q v) m)
  => MaybeT m a
chooseQuorateValues = do
  instanceToChoose <-          gets lnrFirstUnchosenInstance
  acceptanceMap    <- unJust $ gets $ M.lookup instanceToChoose . lnrAcceptances

  forM_ (M.toList acceptanceMap) $ \(proposalId, Acceptances{..}) -> 
    gets (getTopology proposalId . lnrFirstUnchosenTopology) >>= \case
      Just quorum | isQuorum quorum accSet && not (S.null accSet) -> do
        lift $ modify $ \s -> s
          { lnrFirstUnchosenTopology = pushTopology accValue $ lnrFirstUnchosenTopology s }
        lift $ tellChosen instanceToChoose accValue
        chooseQuorateValues
      _ -> return ()

  exitLearner

tellChosen
  :: (MonadEmitter m, Emitted m ~ ChosenMessage q v, MonadState (LearnerState q v) m)
  => InstanceId -> Value q v -> m ()
tellChosen instanceId value = do
  emit $ Chosen instanceId value
  modify $ \s -> s { lnrFirstUnchosenInstance = max (suc instanceId) (lnrFirstUnchosenInstance s) }
