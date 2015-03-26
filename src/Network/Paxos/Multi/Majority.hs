{-# LANGUAGE TypeFamilies #-}

module Network.Paxos.Multi.Majority where

import qualified Data.Set as S

import Network.Paxos.Multi.Types

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
