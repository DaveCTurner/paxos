{-# LANGUAGE PatternGuards #-}

{- Paxos - Implementations of Paxos-related consensus algorithms
 -
 - Copyright (C) 2012  Nicolas Trangez
 -
 - This library is free software; you can redistribute it and/or
 - modify it under the terms of the GNU Lesser General Public
 - License as published by the Free Software Foundation; either
 - version 2.1 of the License, or (at your option) any later version.
 -
 - This library is distributed in the hope that it will be useful,
 - but WITHOUT ANY WARRANTY; without even the implied warranty of
 - MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 - Lesser General Public License for more details.
 -
 - You should have received a copy of the GNU Lesser General Public
 - License along with this library; if not, write to the Free Software
 - Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301
 - USA.
 -}

module Network.Paxos.Synod.Proposer (
    -- * Proposer functionality
      ProposerState
    , Action(..)
    , startRound
    , handlePromise

    -- * Re-exports of useful ProposalId functions
    , ProposalId
    , initialProposalId
    , succProposalId

    -- * Testing
    , tests
    ) where

import Control.Applicative

import Data.Maybe (isNothing)

import Data.Word (Word32)
import Data.Serialize
import Data.Serialize.QuickCheck

import Test.Framework (Test, testGroup)
import Test.Framework.Providers.QuickCheck2 (testProperty)

import Test.QuickCheck (Arbitrary, arbitrary)

import qualified Data.Set as Set
import Data.Set(Set)

import Network.Paxos.Synod.Action
import Network.Paxos.Synod.Types hiding (quorum, tests)
import Network.Paxos.Synod.Messages hiding (tests)

-- | State of a Proposer
data ProposerState nodeId value = ProposerState { proposalId :: ProposalId nodeId
                                                , quorum :: Quorum
                                                , value :: value
                                                , acceptors :: Set nodeId
                                                , highestAccepted :: Maybe (AcceptedValue nodeId value)
                                                }
  deriving (Show, Eq)

serial :: Word32
serial = 0x20121213

instance (Ord nodeId, Serialize nodeId, Serialize value) => Serialize (ProposerState nodeId value) where
    get = do
        serial' <- getWord32le
        if serial' /= serial
            then fail "ProposerState: invalid serial"
            else ProposerState <$> get <*> get <*> get <*> get <*> get
    put (ProposerState a b c d e) = putWord32le serial >> put a >> put b >> put c >> put d >> put e

instance (Ord nodeId, Arbitrary nodeId, Arbitrary value) => Arbitrary (ProposerState nodeId value) where
    arbitrary = ProposerState <$> arbitrary <*> arbitrary <*> arbitrary <*> (Set.fromList <$> arbitrary) <*> arbitrary


-- | Start a single round using given quorum, `ProposalId' and value to propose
startRound :: Quorum  -- ^ Quorum size
           -> ProposalId nodeId  -- ^ `ProposalId' to use
           -> value  -- ^ Value to propose
           -> (ProposerState nodeId value, [Action nodeId value])
startRound quorum' proposalId' value' = (state, [msg])
  where
    state = ProposerState { proposalId = proposalId'
                          , quorum = quorum'
                          , value = value'
                          , acceptors = Set.empty
                          , highestAccepted = Nothing
                          }
    msg = Broadcast Acceptors $ MsgPrepare $ Prepare proposalId'

prop_startRound1 :: Quorum -> ProposalId Int -> () -> Bool
prop_startRound1 q p v = and [ proposalId s == p
                             , quorum s == q
                             , value s == v
                             , Set.null $ acceptors s
                             , isNothing $ highestAccepted s
                             ]
  where
    (s, _) = startRound q p v

prop_startRound2 :: Quorum -> ProposalId Int -> () -> Bool
prop_startRound2 q p v = actions == [Broadcast Acceptors $ MsgPrepare $ Prepare p]
  where
    (_, actions) = startRound q p v


-- | Handle a single `Promise' message received from an Acceptor
handlePromise :: Ord nodeId => ProposerState nodeId value  -- ^ Current state
                            -> nodeId  -- ^ Identifier of the node from which the message was received
                            -> Promise nodeId value  -- ^ Received message
                            -> (ProposerState nodeId value, [Action nodeId value])
handlePromise state acceptor (Promise proposalId' highestAccepted')
    | proposalId' == proposalId state
    = let state' = state { acceptors = Set.insert acceptor $ acceptors state
                         , highestAccepted = max (highestAccepted state) highestAccepted'
                         }
      in (state'
      , if Set.size (acceptors state') == fromIntegral (unQuorum $ quorum state')
        && not (acceptor `Set.member` acceptors state)
          then [ Broadcast Acceptors
               $ MsgAccept
               $ Accept (proposalId state')
               $ maybe (value state') (\(AcceptedValue _ v) -> v) (highestAccepted state')
               ]
          else [])

    | otherwise = (state, [])
    -- TODO Give up if proposal exceeded?

prop_handlePromise :: ProposerState Int ()
                   -> Int
                   -> Promise Int ()
                   -> Bool
prop_handlePromise state acceptor p@(Promise proposalId' highestAccepted')
    | proposalId' /= proposalId state = result == (state, [])
    | otherwise =
        if acceptor `Set.member` acceptors state
            then result == (state, [])
            else and [ acceptor `Set.member` acceptors state'
                     , Set.size (acceptors state') == Set.size (acceptors state) + 1
                     , highestAccepted state' == max (highestAccepted state) highestAccepted'
                     , proposalId state' == proposalId state
                     , (Set.size (acceptors state') /= fromIntegral (unQuorum $ quorum state')) ||
                           (actions == [Broadcast Acceptors $ MsgAccept $ Accept (proposalId state') value'])
                     ]
  where
    result@(state', actions) = handlePromise state acceptor p
    value' = maybe (value state') (\(AcceptedValue _ v) -> v) (highestAccepted state')


-- | Tests
tests :: Test
tests = testGroup "Network.Paxos.Synod.Proposer" [
              testProperty "startRound1" prop_startRound1
            , testProperty "startRound2" prop_startRound2
            , testProperty "handlePromise" prop_handlePromise
            , testProperty "ProposerState Seralize" $ prop_serialize (undefined :: ProposerState String Int)
            ]
