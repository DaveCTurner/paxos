{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE LambdaCase #-}

module Network.Paxos.Multi.Learner where

import Control.Applicative
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Trans.Maybe
import Control.Monad.Writer
import Data.Void
import qualified Data.Map as M
import qualified Data.Set as S

import Network.Paxos.Multi.Types

data LearnerState q v = LearnerState
  { lnrAcceptances       :: M.Map InstanceId (M.Map ProposalId (S.Set AcceptorId))
  , lnrLastValueAccepted :: M.Map InstanceId (M.Map ProposalId (Value q v))
  , lnrChosenValues      :: M.Map InstanceId (AcceptedValue q v)
  , lnrTopologyVersionForFirstUnchosenInstance :: TopologyVersion
  , lnrTopologyForFirstUnchosenInstance        :: q
  , lnrTopologyBeforeFirstUnchosenInstance     :: q
  }

lnrNextInstanceToChoose :: LearnerState q v -> InstanceId
lnrNextInstanceToChoose = maybe (InstanceId 0) (suc . fst . fst) . M.maxViewWithKey . lnrChosenValues

handleAccepted
  :: (MonadWriter [ChosenMessage q v] m, MonadState (LearnerState q v) m, Quorum q)
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

        oldNextInstanceToChoose <- gets lnrNextInstanceToChoose
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

chooseQuorateValues :: (Quorum q, MonadWriter [ChosenMessage q v] m, MonadState (LearnerState q v) m)
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
  :: (MonadWriter [ChosenMessage q v] m, MonadState (LearnerState q v) m)
  => InstanceId -> ProposalId -> Value q v -> m ()
tellChosen instanceId proposalId value = do
  tell [Chosen instanceId value]
  modify $ \s -> s { lnrChosenValues
    = M.insertWith max instanceId (AcceptedValue proposalId value)
      $ lnrChosenValues s }
