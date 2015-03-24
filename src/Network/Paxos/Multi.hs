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
  | NoOp
  | OtherValue v

instance (Show (Alteration q), Show q, Show v) => Show (Value q v)
  where
  show (AlterTopology a) = "AlterTopology (" ++ show a ++ ")"
  show (SetTopology q) = "SetTopology (" ++ show q ++ ")"
  show  NoOp = "NoOp"
  show (OtherValue v) = "OtherValue (" ++ show v ++ ")"

data PrepareType         = MultiPrepare | SinglePrepare
data PromiseType     q v = MultiPromise | Free | Bound ProposalId (Value q v)
data PrepareMessage      = Prepare  InstanceId ProposalId PrepareType
data PromisedMessage q v = Promised InstanceId ProposalId (PromiseType q v)
data ProposedMessage q v = Proposed InstanceId ProposalId (Value q v)
data AcceptedMessage q v = Accepted InstanceId ProposalId (Value q v)
data ChosenMessage   q v = Chosen   InstanceId (Value q v)

data AcceptedValue q v = AcceptedValue ProposalId (Value q v)

valueFromAccepted :: AcceptedValue q v -> Value q v
valueFromAccepted (AcceptedValue _ v) = v

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
  , accMasterLease                :: Maybe (ProposerId, UTCTime)
  }

-- TODO handling master leases could be outside the core
whenOkProposer :: MonadState (AcceptorState q v) m => UTCTime -> ProposalId -> m () -> m ()
whenOkProposer t p go = do
    isOk <- gets $ checkLease . accMasterLease
    when isOk go
  where
  checkLease Nothing = True
  checkLease (Just (masterPid, expiryTime))
    = t <= expiryTime  &&  masterPid == pidProposerId p

boundFromAccepted :: AcceptedValue q v -> PromiseType q v
boundFromAccepted (AcceptedValue p v) = Bound p v

handlePrepare
  :: (MonadWriter [PromisedMessage q v] m, MonadState (AcceptorState q v) m)
  => UTCTime -> PrepareMessage -> m ()
handlePrepare time (Prepare instanceId proposalId MultiPrepare) = whenOkProposer time proposalId $ do

  acceptances <- acceptancesNotBefore instanceId

  let allAcceptancesBefore = case M.maxViewWithKey acceptances of
        Nothing                            -> instanceId
        Just ((maxAcceptedInstance, _), _) -> succ maxAcceptedInstance

  let pidMap = M.unionWith max
        (M.map Just acceptances)
        (M.fromAscList [(i, Nothing) | i <- takeWhile (< allAcceptancesBefore) [instanceId..]])

  forM_ (M.toList pidMap) $ \(i, maybeAcceptedProposalValue)
    -> tellPromise i proposalId $ maybe Free boundFromAccepted maybeAcceptedProposalValue
  tellPromise allAcceptancesBefore proposalId MultiPromise

handlePrepare time (Prepare instanceId proposalId SinglePrepare) = whenOkProposer time proposalId $ do
  maybeCurrentAcceptance <- gets $ M.lookup instanceId . accLatestAcceptanceByInstance
  tellPromise instanceId proposalId $ maybe Free boundFromAccepted maybeCurrentAcceptance

acceptancesNotBefore :: MonadState (AcceptorState q v) m
  => InstanceId -> m (M.Map InstanceId (AcceptedValue q v))
acceptancesNotBefore instanceId = do
  (_, maybeCurrentAcceptance, futureAcceptances)
    <- gets $ M.splitLookup instanceId . accLatestAcceptanceByInstance
  return $ maybe id (M.insert instanceId) maybeCurrentAcceptance
         $ futureAcceptances

handleProposed
  :: (MonadWriter [AcceptedMessage q v] m, MonadState (AcceptorState q v) m)
  => UTCTime -> (ProposedMessage q v) -> m ()
handleProposed time (Proposed instanceId proposalId value) = whenOkProposer time proposalId $ do

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

data LearnerState q v = LearnerState
  { lnrAcceptances       :: M.Map InstanceId (M.Map ProposalId (S.Set AcceptorId))
  , lnrLastValueAccepted :: M.Map InstanceId (M.Map ProposalId (Value q v))
  , lnrChosenValues      :: M.Map InstanceId (AcceptedValue q v)
  , lnrTopologyVersionForFirstUnchosenInstance :: TopologyVersion
  , lnrTopologyForFirstUnchosenInstance        :: q
  , lnrTopologyBeforeFirstUnchosenInstance     :: q
  }

lnrNextInstanceToChoose :: LearnerState q v -> InstanceId
lnrNextInstanceToChoose = maybe (InstanceId 0) (succ . fst . fst) . M.maxViewWithKey . lnrChosenValues

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

        oldNextInstanceToChoose <- gets lnrNextInstanceToChoose
        newNextInstanceToChoose <- runLearnerT chooseQuorateValues oldNextInstanceToChoose

        -- TODO the rest of this could be outside the core
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
      then s { pprMinMultiInstance = succ instanceId
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
  forM_ (takeWhile (< newMinMultiInstance) $ iterate succ oldMinMultiInstance) $ \newInstance -> do
    s <- get

    promisesState <- execStateT (checkIfReady $ pprTopology s) CollectingPromises
                        { cprPromises = pprPromises s
                        , cprMaxAccepted = Nothing
                        }

    put $ s
      { pprMinMultiInstance = succ newInstance
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
  forM_ (takeWhile (< minMultiInstance) $ iterate succ instanceId) $ \existingInstance
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
  spawnInstanceProposersTo $ succ instanceId
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
