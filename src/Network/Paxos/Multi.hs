{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE LambdaCase #-}

module Network.Paxos.Multi where

import Control.Applicative
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Trans.Maybe
import Control.Monad.Writer
import Data.Maybe
import Data.Time
import Data.Void
import qualified Data.Map as M
import qualified Data.RangeMap as RM
import qualified Data.Set as S

newtype InstanceId = InstanceId Integer deriving (Show, Eq, Ord, Enum)
newtype TopologyVersion = TopologyVersion Integer deriving (Show, Eq, Ord, Enum)
newtype AcceptorId = AcceptorId Integer deriving (Show, Eq, Ord)

newtype ProposalNumber = ProposalNumber Integer deriving (Show, Eq, Ord)
newtype ProposerId = ProposerId Integer deriving (Show, Eq, Ord)

data ProposalId = ProposalId
  { pidTopologyVersion :: TopologyVersion
  , pidProposal        :: ProposalNumber
  , pidProposerId      :: ProposerId
  } deriving (Show, Eq, Ord)

class Quorum q where
  type Alteration q

  noQuorums :: q
  isQuorum :: q -> S.Set AcceptorId -> Bool
  alterQuorum :: Alteration q -> q -> q

data MajorityOf = MajorityOf (S.Set AcceptorId)
  deriving (Show, Eq)

data MajorityAlteration = AddAcceptor AcceptorId | RemoveAcceptor AcceptorId
  deriving (Show, Eq)

instance Quorum MajorityOf where
  type Alteration MajorityOf = MajorityAlteration

  noQuorums = MajorityOf S.empty
  isQuorum (MajorityOf voters) s
      = not (S.null voters)
      && S.size (S.intersection voters s) * 2 > S.size voters
  alterQuorum (AddAcceptor    a) (MajorityOf vs) = MajorityOf (S.insert a vs)
  alterQuorum (RemoveAcceptor a) (MajorityOf vs) = MajorityOf (S.delete a vs)

data Value q v
  = AlterTopology (Alteration q)
  | SetTopology q
  | MasterLease ProposerId UTCTime
  | OtherValue v

instance (Show (Alteration q), Show q, Show v) => Show (Value q v)
  where
  show (AlterTopology a) = "AlterTopology (" ++ show a ++ ")"
  show (SetTopology q) = "SetTopology (" ++ show q ++ ")"
  show (MasterLease p t) = "MasterLease (" ++ show p ++ ") (" ++ show t ++ ")"
  show (OtherValue v) = "OtherValue (" ++ show v ++ ")"

data PromiseType     q v = Multi | Free | Bound ProposalId (Value q v)
data PrepareMessage      = Prepare  InstanceId ProposalId
data PromisedMessage q v = Promised InstanceId ProposalId (PromiseType q v)
data ProposedMessage q v = Proposed InstanceId ProposalId (Value q v)
data AcceptedMessage q v = Accepted InstanceId ProposalId (Value q v)
data ChosenMessage   q v = Chosen   InstanceId (Value q v)

data AcceptedValue q v = AcceptedValue ProposalId (Value q v)

instance Eq (AcceptedValue q v) where
  AcceptedValue p1 _ == AcceptedValue p2 _ = p1 == p2
  AcceptedValue p1 _ /= AcceptedValue p2 _ = p1 /= p2

instance Ord (AcceptedValue q v) where
  AcceptedValue p1 _ <= AcceptedValue p2 _ = p1 <= p2
  AcceptedValue p1 _ <  AcceptedValue p2 _ = p1 <  p2
  AcceptedValue p1 _ >= AcceptedValue p2 _ = p1 >= p2
  AcceptedValue p1 _ >  AcceptedValue p2 _ = p1 >  p2
  compare (AcceptedValue p1 _) (AcceptedValue p2 _) = compare p1 p2

data AcceptorState q v = AcceptorState
  { accMinAcceptableProposal      :: RM.RangeMap InstanceId ProposalId
  , accLatestAcceptanceByInstance :: M.Map InstanceId (AcceptedValue q v)
  }

handlePrepare
  :: (MonadWriter [PromisedMessage q v] m, MonadState (AcceptorState q v) m)
  => PrepareMessage -> m ()
handlePrepare (Prepare instanceId proposalId) = do

  acceptances <- acceptancesNotBefore instanceId

  let allAcceptancesBefore = case M.maxViewWithKey acceptances of
        Nothing                            -> instanceId
        Just ((maxAcceptedInstance, _), _) -> succ maxAcceptedInstance

  let pidMap = M.unionWith max
        (M.map Just acceptances)
        (M.fromAscList [(i, Nothing) | i <- takeWhile (< allAcceptancesBefore) [instanceId..]])

  let mkBound (AcceptedValue p v) = Bound p v

  forM_ (M.toList pidMap) $ \(i, maybeAcceptedProposalValue)
    -> tellPromise i proposalId $ maybe Free mkBound maybeAcceptedProposalValue
  tellPromise allAcceptancesBefore proposalId Multi

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

  -- TODO reject proposals from non-master proposer during lease.

  when isAcceptable $ tellAccept instanceId proposalId value

tellPromise
  :: (MonadWriter [PromisedMessage q v] m, MonadState (AcceptorState q v) m)
  => InstanceId -> ProposalId -> (PromiseType q v) -> m ()
tellPromise i p t = do
  let msg = Promised i p t
  tell [msg]
  let promiseRange = case t of
        Multi -> RM.inclusiveUnbounded i
        _     -> RM.inclusiveInclusive i i
  modify $ \s -> s { accMinAcceptableProposal = RM.insertWith max promiseRange p $ accMinAcceptableProposal s }

tellAccept
  :: (MonadWriter [AcceptedMessage q v] m, MonadState (AcceptorState q v) m)
  => InstanceId -> ProposalId -> Value q v -> m ()
tellAccept i p v = do
  tell [Accepted i p v]
  modify $ \s -> s { accLatestAcceptanceByInstance
      = M.insertWith max i (AcceptedValue p v) $ accLatestAcceptanceByInstance s }

data LearnerState q v = LearnerState
  { lnrAcceptances       :: M.Map InstanceId (M.Map ProposalId (S.Set AcceptorId))
  , lnrLastValueAccepted :: M.Map InstanceId (M.Map ProposalId (Value q v))
  , lnrChosenValues      :: M.Map InstanceId (AcceptedValue q v)
  , lnrTopologyVersionForFirstUnchosenInstance :: TopologyVersion
  , lnrTopologyForFirstUnchosenInstance        :: q
  , lnrTopologyBeforeFirstUnchosenInstance     :: q
  }

handleAccepted
  :: (MonadWriter [ChosenMessage q v] m, MonadState (LearnerState q v) m, Quorum q)
  => AcceptorId -> AcceptedMessage q v -> m ()
handleAccepted acceptorId (Accepted instanceId proposalId value) = do

  maybeChosenValue <- gets $ M.lookup instanceId . lnrChosenValues

  case maybeChosenValue of
    Just (AcceptedValue chosenProposal chosenValue)
      -> when (chosenProposal < proposalId)
          $ tellChosen instanceId proposalId chosenValue

    Nothing -> do
      minInstanceTopologyVersion <- gets lnrTopologyVersionForFirstUnchosenInstance

      when (minInstanceTopologyVersion <= succ (pidTopologyVersion proposalId)) $ do

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

        oldNextInstanceToChoose <- gets $ maybe (InstanceId 0) (succ . fst . fst) . M.maxViewWithKey . lnrChosenValues
        newNextInstanceToChoose <- runLearnerT chooseQuorateValues oldNextInstanceToChoose
        newMinInstanceTopologyVersion <- gets lnrTopologyVersionForFirstUnchosenInstance

        when (oldNextInstanceToChoose < newNextInstanceToChoose) $ do

          let removeOldTopologies :: M.Map ProposalId a -> M.Map ProposalId a
              removeOldTopologies = M.filterWithKey (\pid _ -> newMinInstanceTopologyVersion <= succ (pidTopologyVersion pid))

              removeChosenInstances :: M.Map InstanceId a -> M.Map InstanceId a
              removeChosenInstances = snd . M.split (pred newNextInstanceToChoose)

              tidyMap :: M.Map InstanceId (M.Map ProposalId a) -> M.Map InstanceId (M.Map ProposalId a)
              tidyMap = M.map removeOldTopologies . removeChosenInstances

          modify $ \s -> s
            { lnrAcceptances       = tidyMap $ lnrAcceptances s
            , lnrLastValueAccepted = tidyMap $ lnrLastValueAccepted s
            }

newtype LearnerT m a = LearnerT (MaybeT (StateT InstanceId m) a)
  deriving (Functor, Applicative, Monad)

instance MonadTrans LearnerT where
  lift = LearnerT . lift . lift

runLearnerT :: Monad m => LearnerT m Void -> InstanceId -> m InstanceId
runLearnerT (LearnerT go) = execStateT (runMaybeT go)

getNextInstance :: Monad m => LearnerT m InstanceId
getNextInstance = LearnerT $ lift get

advanceInstance :: Monad m => LearnerT m ()
advanceInstance = LearnerT $ lift $ modify succ

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
        | instanceTopologyVersion ==       proposalTopologyVersion  = lnrTopologyForFirstUnchosenInstance
        | instanceTopologyVersion == succ (proposalTopologyVersion) = lnrTopologyBeforeFirstUnchosenInstance
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
            = succ (lnrTopologyVersionForFirstUnchosenInstance s)
          , lnrTopologyForFirstUnchosenInstance    = alterQuorum alteration (lnrTopologyForFirstUnchosenInstance s)
          , lnrTopologyBeforeFirstUnchosenInstance = lnrTopologyForFirstUnchosenInstance s
          }

        SetTopology newTopology -> lift $ modify $ \s -> s
          { lnrTopologyVersionForFirstUnchosenInstance
            = succ (succ (lnrTopologyVersionForFirstUnchosenInstance s))
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

