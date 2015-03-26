{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RecordWildCards #-}

module Network.Paxos.Multi.Types where

import qualified Data.Set as S

class HasSuccessor a where
  suc :: a -> a

newtype InstanceId = InstanceId Integer deriving (Show, Eq, Ord)
newtype TopologyVersion = TopologyVersion Integer deriving (Show, Eq, Ord)

instance HasSuccessor InstanceId      where suc (InstanceId i)      = InstanceId (i + 1)
instance HasSuccessor TopologyVersion where suc (TopologyVersion v) = TopologyVersion (v + 1)

newtype AcceptorId = AcceptorId Integer deriving (Show, Eq, Ord)

newtype ProposalNumber = ProposalNumber Integer deriving (Show, Eq, Ord)
newtype ProposerId = ProposerId Integer deriving (Show, Eq, Ord)

data ProposalId = ProposalId
  { pidTopologyVersion :: TopologyVersion
  , pidProposal        :: ProposalNumber
  , pidProposerId      :: ProposerId
  } deriving (Show, Eq, Ord)

class MonadEmitter m where
  type Emitted m
  emit :: Emitted m -> m ()

class Quorum q where
  type Alteration q

  noQuorums :: q
  isQuorum :: q -> S.Set AcceptorId -> Bool
  alterQuorum :: Alteration q -> q -> q

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

data TopologyHistory q = TopologyHistory
  { topoCurr :: q
  , topoPrev :: q
  , topoVersion :: TopologyVersion
  }

initialTopology :: Quorum q => q -> TopologyHistory q
initialTopology topology = TopologyHistory
  { topoCurr    = topology
  , topoPrev    = noQuorums
  , topoVersion = TopologyVersion 0
  }

pushTopology :: Quorum q => Value q v -> TopologyHistory q -> TopologyHistory q
pushTopology (AlterTopology alteration) TopologyHistory{..} = TopologyHistory
  { topoCurr    = alterQuorum alteration topoCurr
  , topoPrev    =                        topoCurr
  , topoVersion = suc topoVersion
  }
pushTopology (SetTopology topology) TopologyHistory{..} = TopologyHistory
  { topoCurr    = topology
  , topoPrev    = noQuorums
  , topoVersion = suc (suc topoVersion)
  }
pushTopology _ th = th

getTopology :: Quorum q => ProposalId -> TopologyHistory q -> Maybe q
getTopology ProposalId{..} TopologyHistory{..}
  | topoVersion ==     pidTopologyVersion = Just topoCurr
  | topoVersion == suc pidTopologyVersion = Just topoPrev
  | otherwise = Nothing

data PrepareType         = MultiPrepare | SinglePrepare
data PromiseType     q v = MultiPromise | Free | Bound ProposalId (Value q v)
data PrepareMessage      = Prepare  InstanceId ProposalId PrepareType
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

boundFromAccepted :: AcceptedValue q v -> PromiseType q v
boundFromAccepted (AcceptedValue p v) = Bound p v

valueFromAccepted :: AcceptedValue q v -> Value q v
valueFromAccepted (AcceptedValue _ v) = v

