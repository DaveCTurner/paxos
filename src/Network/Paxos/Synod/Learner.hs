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

module Network.Paxos.Synod.Learner (
    -- * Learner functionality
      LearnerState
    , initialize
    -- ** Incoming message handlers
    , handleAccepted
    -- ** Result extraction
    , getValue
    -- * Testing
    , tests
    ) where

import Control.Applicative

import Data.Maybe (isNothing)

import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set

import Data.Word (Word32)
import Data.Serialize
import Data.Serialize.QuickCheck

import Test.Framework (Test, testGroup)
import Test.Framework.Providers.QuickCheck2 (testProperty)

import Test.QuickCheck (Arbitrary, arbitrary, oneof)

import Network.Paxos.Synod.Types hiding (quorum, tests)
import Network.Paxos.Synod.Messages hiding (tests)

-- | State of a Learner
data LearnerState nodeId value = Learning { quorum :: Quorum
                                          , accepted :: Map (ProposalId nodeId) (Set nodeId)
                                          }
                               | Decided value
  deriving (Show, Eq)

serial :: Word32
serial = 0x20121214

instance (Ord nodeId, Serialize nodeId, Serialize value) => Serialize (LearnerState nodeId value) where
    get = do
        serial' <- getWord32le
        if serial' /= serial
            then fail "LearnerState: invalid serial"
            else do
                tag <- getWord8
                case tag of
                    1 -> Learning <$> get <*> get
                    2 -> Decided <$> get
                    _ -> fail "LearnerState: invalid tag"

    put state = do
        putWord32le serial
        case state of
            Learning a b -> putWord8 1 >> put a >> put b
            Decided a -> putWord8 2 >> put a

instance (Ord nodeId, Arbitrary nodeId, Arbitrary value) => Arbitrary (LearnerState nodeId value) where
    arbitrary = oneof [learning, decided]
      where
        decided = Decided <$> arbitrary
        learning = do
            state0 <- initialize <$> arbitrary
            mods <- arbitrary
            let f (nodeId, msg) s = case handleAccepted s nodeId msg of
                                        Decided _ -> s
                                        s'@Learning{} -> s'
                state = foldr f state0 mods
            return state


-- | Generate an initial Learner state
initialize :: Quorum  -- ^ Number of nodes which form a quorum
           -> LearnerState nodeId value
initialize quorum' = Learning { quorum = quorum'
                              , accepted = Map.empty
                              }

prop_initialize :: Quorum -> Bool
prop_initialize quorum' = and [ isNothing $ getValue state
                              , quorum state == quorum'
                              , Map.null $ accepted state
                              ]
  where
    state = initialize quorum'


-- | Handle a single Accepted message received from an Acceptor
handleAccepted :: Ord nodeId
               => LearnerState nodeId value  -- ^ Current state
               -> nodeId  -- ^ Identifier of the node from which the message was received
               -> Accepted nodeId value  -- ^ Received message
               -> LearnerState nodeId value
handleAccepted state acceptor (Accepted proposalId value) =
    case state of
        Decided _ -> state
        Learning{} -> case Map.lookup proposalId accepted' of
          Just s | Set.size s == fromIntegral (unQuorum (quorum state)) -> Decided value
          _ -> state { accepted = accepted' }

  where
    accepted' = Map.insertWith Set.union proposalId (Set.singleton acceptor) (accepted state)

-- | Extract the learned value from the Learner state, if any.
--
-- Once a value has been learned, handling more `Prepare' messages becomes
-- a no-op.
getValue :: LearnerState nodeId value -> Maybe value
getValue state = case state of
    Learning{} -> Nothing
    Decided value -> Just value

prop_getValue :: LearnerState Int Int -> Bool
prop_getValue state = case state of
    Decided value -> getValue state == Just value
    Learning{} -> isNothing $ getValue state


-- | Tests
tests :: Test
tests = testGroup "Network.Paxos.Synod.Learner" [
              testProperty "initialize" prop_initialize
            , testProperty "getValue" prop_getValue
            , testProperty "LearnerState Serialize" $ prop_serialize (undefined :: LearnerState String Int)
            ]
