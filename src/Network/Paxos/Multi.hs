{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleContexts #-}

module Network.Paxos.Multi where

import Control.Monad.Reader
import Control.Monad.Writer
import Control.Monad.State
import qualified Data.Map as M
import qualified Data.RangeMap as RM
import qualified Data.Set as S
import Data.Time

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

data Value v
  = AddAcceptor AcceptorId
  | DelAcceptor AcceptorId
  | CommitTopologyChange
  | MasterLease ProposerId UTCTime
  | OtherValue v
  deriving (Show, Eq, Ord)

data PromiseType v = Multi | Free | Bound ProposalId (Value v)
  deriving (Show, Eq, Ord)

data PrepareMessage
  = Prepare  InstanceId ProposalId
  deriving (Show, Eq, Ord)

data PromisedMessage v
  = Promised InstanceId ProposalId (PromiseType v)
  deriving (Show, Eq, Ord)

data ProposedMessage v
  = Proposed InstanceId ProposalId (Value v)
  deriving (Show, Eq, Ord)

data AcceptedMessage v
  = Accepted InstanceId ProposalId (Value v)
  deriving (Show, Eq, Ord)

data ChosenMessage v
  = Chosen   InstanceId (Value v)
  deriving (Show, Eq, Ord)

data AcceptedValue v = AcceptedValue ProposalId (Value v)

instance Eq (AcceptedValue v) where
  AcceptedValue p1 _ == AcceptedValue p2 _ = p1 == p2
  AcceptedValue p1 _ /= AcceptedValue p2 _ = p1 /= p2

instance Ord (AcceptedValue v) where
  AcceptedValue p1 _ <= AcceptedValue p2 _ = p1 <= p2
  AcceptedValue p1 _ <  AcceptedValue p2 _ = p1 <  p2
  AcceptedValue p1 _ >= AcceptedValue p2 _ = p1 >= p2
  AcceptedValue p1 _ >  AcceptedValue p2 _ = p1 >  p2
  compare (AcceptedValue p1 _) (AcceptedValue p2 _) = compare p1 p2

data AcceptorState v = AcceptorState
  { accMinAcceptableProposal      :: RM.RangeMap InstanceId ProposalId
  , accLatestAcceptanceByInstance :: M.Map InstanceId (AcceptedValue v)
  }

handlePrepare
  :: (MonadWriter [PromisedMessage v] m, MonadState (AcceptorState v) m)
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

acceptancesNotBefore :: MonadState (AcceptorState v) m
  => InstanceId -> m (M.Map InstanceId (AcceptedValue v))
acceptancesNotBefore instanceId = do  
  (_, maybeCurrentAcceptance, futureAcceptances)
    <- gets $ M.splitLookup instanceId . accLatestAcceptanceByInstance 
  return $ maybe id (M.insert instanceId) maybeCurrentAcceptance
         $ futureAcceptances

handleProposed
  :: (MonadWriter [AcceptedMessage v] m, MonadState (AcceptorState v) m)
  => (ProposedMessage v) -> m ()
handleProposed (Proposed instanceId proposalId value) = do

  maybeMinAcceptableProposal <- gets $ RM.lookup instanceId . accMinAcceptableProposal

  let isAcceptable = case maybeMinAcceptableProposal of
          Nothing -> True
          Just minAcceptableProposal -> minAcceptableProposal <= proposalId

  -- TODO reject proposals from non-master proposer during lease.

  when isAcceptable $ tellAccept instanceId proposalId value

tellPromise
  :: (MonadWriter [PromisedMessage v] m, MonadState (AcceptorState v) m)
  => InstanceId -> ProposalId -> (PromiseType v) -> m ()
tellPromise i p t = do
  let msg = Promised i p t
  tell [msg]
  let promiseRange = case t of
        Multi -> RM.inclusiveUnbounded i
        _     -> RM.inclusiveInclusive i i
  modify $ \s -> s { accMinAcceptableProposal = RM.insertWith max promiseRange p $ accMinAcceptableProposal s }

tellAccept
  :: (MonadWriter [AcceptedMessage v] m, MonadState (AcceptorState v) m)
  => InstanceId -> ProposalId -> Value v -> m ()
tellAccept i p v = do
  tell [Accepted i p v]
  modify $ \s -> s { accLatestAcceptanceByInstance
      = M.insertWith max i (AcceptedValue p v) $ accLatestAcceptanceByInstance s }

data LearnerState v = LearnerState
  { lnrAcceptances       :: M.Map InstanceId (M.Map ProposalId (S.Set AcceptorId))
  , lnrLastValueAccepted :: M.Map InstanceId (M.Map ProposalId (Value v))
  , lnrTopologies        :: RM.RangeMap Integer (S.Set AcceptorId -> Bool)
  , lnrTopologyVersions  :: RM.RangeMap InstanceId Integer
  , lnrChosenValues      :: M.Map InstanceId (AcceptedValue v)
  }

handleAccepted
  :: (MonadWriter [ChosenMessage v] m, MonadState (LearnerState v) m)
  => AcceptorId -> AcceptedMessage v -> m ()
handleAccepted acceptorId (Accepted instanceId proposalId value) = do

  maybeChosenValue <- gets $ M.lookup instanceId . lnrChosenValues

  case maybeChosenValue of
    Just (AcceptedValue chosenProposal chosenValue)
      -> when (chosenProposal < proposalId)
          $ tellChosen instanceId proposalId chosenValue

    Nothing -> do
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
      newNextInstanceToChoose <- chooseQuorateValues oldNextInstanceToChoose

      when (oldNextInstanceToChoose < newNextInstanceToChoose) $ do
        let tidyMap = snd . M.split (pred newNextInstanceToChoose)
        modify $ \s -> s
          { lnrAcceptances       = tidyMap $ lnrAcceptances s
          , lnrLastValueAccepted = tidyMap $ lnrLastValueAccepted s
          , lnrTopologies        = ($ lnrTopologies s)
              $ case RM.lookup newNextInstanceToChoose (lnrTopologyVersions s) of
                  Nothing -> id
                  Just tv -> RM.delete (RM.unboundedExclusive tv)
          , lnrTopologyVersions  = RM.delete (RM.unboundedExclusive newNextInstanceToChoose)
              $ lnrTopologyVersions s
          }

chooseQuorateValues :: (MonadWriter [ChosenMessage v] m, MonadState (LearnerState v) m)
  => InstanceId -> m InstanceId
chooseQuorateValues instanceId = do
  maybeTopologyVersion <- gets $ RM.lookup instanceId . lnrTopologyVersions
  case maybeTopologyVersion of
    Nothing -> return instanceId
    Just tv -> do
      maybeTopology <- gets $ RM.lookup tv . lnrTopologies
      case maybeTopology of
        Nothing -> return instanceId
        Just isQuorum -> do
          acceptances <- gets $ M.toList . fromMaybe M.empty . M.lookup instanceId . lnrAcceptances
          forM_ acceptances $ \(proposalId, acceptanceSet) -> when (isQuorum acceptanceSet) $ do
            maybeProposalValues <- gets $ M.lookup instanceId . lnrLastValueAccepted
            case fmap (M.lookup proposalId) maybeProposalValues of
              Nothing -> return instanceId
              Just proposalValue -> do
                tellChosen instanceId proposalId
                chooseQuorateValues (succ instanceId)
                -- TODO early exit from loop

tellChosen
  :: (MonadWriter [ChosenMessage v] m, MonadState (LearnerState v) m)
  => InstanceId -> ProposalId -> Value v -> m ()
tellChosen instanceId proposalId value = do
  tell [Chosen instanceId value]
  modify $ \s -> s { lnrChosenValues
    = M.insertWith max instanceId (AcceptedValue proposalId value)
      $ lnrChosenValues s }


