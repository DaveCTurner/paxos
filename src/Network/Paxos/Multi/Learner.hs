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

module Network.Paxos.Multi.Learner
  ( LearnerState
  , initialLearnerState
  , joiningLearnerState
  , nextInstance
  , nextInstanceTopology
  , nextInstanceTopologyVersion
  , handleAccepted
  ) where

import Control.Applicative
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Trans.Maybe
import Data.Void
import qualified Data.Map as M
import qualified Data.Set as S

import Network.Paxos.Multi.Types

{-| The state of an individual learner. -}
data LearnerState q v = LearnerState
  { lnrAcceptances       :: M.Map InstanceId (M.Map ProposalId (S.Set AcceptorId))
  , lnrLastValueAccepted :: M.Map InstanceId (M.Map ProposalId (Value q v))
  , lnrChosenValues      :: M.Map InstanceId (AcceptedValue q v)
  , lnrTopologyVersionForFirstUnchosenInstance :: TopologyVersion
  , lnrTopologyForFirstUnchosenInstance        :: q
  , lnrTopologyBeforeFirstUnchosenInstance     :: q
  }

{-| The initial state of an individual learner, before it has processed any
messages and before any values have been chosen. -}
initialLearnerState :: Quorum q => TopologyVersion -> q -> LearnerState q v
initialLearnerState v q = LearnerState
  { lnrAcceptances       = M.empty
  , lnrLastValueAccepted = M.empty
  , lnrChosenValues      = M.empty
  , lnrTopologyVersionForFirstUnchosenInstance = v
  , lnrTopologyForFirstUnchosenInstance        = q
  , lnrTopologyBeforeFirstUnchosenInstance     = noQuorums
  }

{-| The starting state of a learner which joins the cluster after it has been
running for a while, so the initial sequence of values has been chosen. It only
needs to know the most recent value and the current and previous topologies.
-}
joiningLearnerState :: InstanceId -> AcceptedValue q v -> TopologyVersion -> q -> q -> LearnerState q v
joiningLearnerState i a v qCurrent qPrevious = LearnerState
  { lnrAcceptances       = M.empty
  , lnrLastValueAccepted = M.empty
  , lnrChosenValues      = M.singleton i a
  , lnrTopologyVersionForFirstUnchosenInstance = v
  , lnrTopologyForFirstUnchosenInstance        = qCurrent
  , lnrTopologyBeforeFirstUnchosenInstance     = qPrevious
  }

{-| Get the id of the first instance whose value has not yet been learned. -}
nextInstance :: LearnerState q v -> InstanceId
nextInstance = maybe (InstanceId 0) (suc . fst . fst) . M.maxViewWithKey . lnrChosenValues

{-| Get the topology of the first instance whose value has not yet been learned. -}
nextInstanceTopology :: LearnerState q v -> q
nextInstanceTopology = lnrTopologyForFirstUnchosenInstance

{-| Get the topology version of the first instance whose value has not yet been learned. -}
nextInstanceTopologyVersion :: LearnerState q v -> TopologyVersion
nextInstanceTopologyVersion = lnrTopologyVersionForFirstUnchosenInstance

{-| Handle an 'AcceptedMessage', which may result in a 'ChosenMessage' indicating that a value
has been chosen. -}
handleAccepted
  :: (MonadEmitter m, Emitted m ~ ChosenMessage q v, MonadState (LearnerState q v) m, Quorum q)
  => AcceptorId -> AcceptedMessage q v -> m ()
handleAccepted acceptorId (Accepted instanceId proposalId value) = do

  maybeChosenValue <- gets $ M.lookup instanceId . lnrChosenValues

  case maybeChosenValue of
    -- TODO this could be outside the core
    Just (AcceptedValue chosenProposal chosenValue)
      -> when (chosenProposal < proposalId)
          $ tellChosen instanceId proposalId chosenValue

    Nothing -> do
      minInstanceTopologyVersion <- gets lnrTopologyVersionForFirstUnchosenInstance

      when (minInstanceTopologyVersion <= suc (pidTopologyVersion proposalId)) $ do

        modify $ \s -> s
          { lnrAcceptances
              = M.insertWith
                    (M.unionWith S.union)
                    instanceId
                    (M.singleton proposalId $ S.singleton acceptorId)
                    (lnrAcceptances s)

          , lnrLastValueAccepted
              = M.insertWith
                    M.union
                    instanceId
                    (M.singleton proposalId value)
                    (lnrLastValueAccepted s)
          }

        oldNextInstanceToChoose <- gets nextInstance
        newNextInstanceToChoose <- runLearnerT chooseQuorateValues oldNextInstanceToChoose

        -- TODO the rest of this could be outside the core
        newMinInstanceTopologyVersion <- gets lnrTopologyVersionForFirstUnchosenInstance

        when (oldNextInstanceToChoose < newNextInstanceToChoose) $ do

          let removeOldTopologies :: M.Map ProposalId a -> M.Map ProposalId a
              removeOldTopologies = M.filterWithKey (\pid _ -> newMinInstanceTopologyVersion <= suc (pidTopologyVersion pid))

              removeChosenInstances :: M.Map InstanceId a -> M.Map InstanceId a
              removeChosenInstances = removeKeysLessThan newNextInstanceToChoose

              tidyMap :: M.Map InstanceId (M.Map ProposalId a) -> M.Map InstanceId (M.Map ProposalId a)
              tidyMap = M.map removeOldTopologies . removeChosenInstances

          modify $ \s -> s
            { lnrAcceptances       = tidyMap $ lnrAcceptances s
            , lnrLastValueAccepted = tidyMap $ lnrLastValueAccepted s
            }

removeKeysLessThan :: InstanceId -> M.Map InstanceId a -> M.Map InstanceId a
removeKeysLessThan instanceId m = case M.splitLookup instanceId m of
  (_, Nothing, m') -> m'
  (_, Just a, m')  -> M.insert instanceId a m'

newtype LearnerT m a = LearnerT (MaybeT (StateT InstanceId m) a)
  deriving (Functor, Applicative, Monad)

instance MonadTrans LearnerT where
  lift = LearnerT . lift . lift

runLearnerT :: Monad m => LearnerT m Void -> InstanceId -> m InstanceId
runLearnerT (LearnerT go) = execStateT (runMaybeT go)

getNextInstance :: Monad m => LearnerT m InstanceId
getNextInstance = LearnerT $ lift get

advanceInstance :: Monad m => LearnerT m ()
advanceInstance = LearnerT $ lift $ modify suc

exitLearner :: Monad m => LearnerT m a
exitLearner = LearnerT mzero

unJust :: Monad m => m (Maybe a) -> LearnerT m a
unJust mma = lift mma >>= \case
  Nothing -> exitLearner
  Just a -> return a

chooseQuorateValues :: (Quorum q, MonadEmitter m, Emitted m ~ ChosenMessage q v, MonadState (LearnerState q v) m)
  => LearnerT m a
chooseQuorateValues = do
  instanceToChoose <- getNextInstance
  instanceTopologyVersion <- lift $ gets lnrTopologyVersionForFirstUnchosenInstance

  let lnrQuorum proposalTopologyVersion
        | instanceTopologyVersion ==      proposalTopologyVersion  = lnrTopologyForFirstUnchosenInstance
        | instanceTopologyVersion == suc (proposalTopologyVersion) = lnrTopologyBeforeFirstUnchosenInstance
        | otherwise = const noQuorums

  acceptanceMap <- unJust $ gets $ M.lookup instanceToChoose . lnrAcceptances

  forM_ (M.toList acceptanceMap) $ \(proposalId, acceptorSet) -> do
    quorum <- lift $ gets $ lnrQuorum $ pidTopologyVersion proposalId
    when (isQuorum quorum acceptorSet) $ do
      lastValuesMap <- unJust $ gets   $ M.lookup instanceToChoose . lnrLastValueAccepted
      chosenValue   <- unJust $ return $ M.lookup proposalId lastValuesMap

      case chosenValue of
        AlterTopology alteration -> lift $ modify $ \s -> s
          { lnrTopologyVersionForFirstUnchosenInstance
            = suc (lnrTopologyVersionForFirstUnchosenInstance s)
          , lnrTopologyForFirstUnchosenInstance    = alterQuorum alteration (lnrTopologyForFirstUnchosenInstance s)
          , lnrTopologyBeforeFirstUnchosenInstance = lnrTopologyForFirstUnchosenInstance s
          }

        SetTopology newTopology -> lift $ modify $ \s -> s
          { lnrTopologyVersionForFirstUnchosenInstance
            = suc (suc (lnrTopologyVersionForFirstUnchosenInstance s))
          , lnrTopologyForFirstUnchosenInstance    = newTopology
          , lnrTopologyBeforeFirstUnchosenInstance = noQuorums
          }

        _ -> return ()

      lift $ tellChosen instanceToChoose proposalId chosenValue
      advanceInstance
      chooseQuorateValues

  exitLearner

tellChosen
  :: (MonadEmitter m, Emitted m ~ ChosenMessage q v, MonadState (LearnerState q v) m)
  => InstanceId -> ProposalId -> Value q v -> m ()
tellChosen instanceId proposalId value = do
  emit $ Chosen instanceId value
  modify $ \s -> s { lnrChosenValues
    = M.insertWith max instanceId (AcceptedValue proposalId value)
      $ lnrChosenValues s }
