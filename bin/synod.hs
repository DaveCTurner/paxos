{-# LANGUAGE LambdaCase #-}

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

module Main (main) where

import Control.Monad

import Control.Concurrent.Async
import Control.Concurrent hiding (readChan, writeChan)
import Control.Concurrent.STM
import System.Timeout

import qualified Control.Concurrent.UnreliableChan as U

import System.Random

import System.IO (stderr)

import System.Log.Logger
import System.Log.Handler (setFormatter)
import System.Log.Handler.Simple (streamHandler)
import System.Log.Formatter

import Network.Paxos.Synod
import qualified Network.Paxos.Synod.Proposer as P
import qualified Network.Paxos.Synod.Acceptor as A
import qualified Network.Paxos.Synod.Learner as L

type NodeId = String
type Value = String
type Actions = [Action NodeId Value]
type NetworkChannel = TChan (NodeId, Action NodeId Value)
type MessageChannel = TChan (NodeId, Message NodeId Value)

lost :: Double
lost = 0.02
minDelay :: Int
minDelay = 1000
maxDelay :: Int
maxDelay = 300000
readChan :: U.Chan a -> IO a
readChan = U.readChan lost (minDelay, maxDelay)
writeChan :: U.Chan a -> a -> IO ()
writeChan = U.writeChan lost (minDelay, maxDelay)

handleActions :: NodeId -> NetworkChannel -> Actions -> IO ()
handleActions name network = mapM_ (\a -> writeChan network (name, a))

runProposer :: MVar Value -> String -> Quorum -> P.ProposalId NodeId -> Value -> MessageChannel -> NetworkChannel -> IO ()
runProposer lock name q p v chan network = do
    info $ "Running proposer for proposal " ++ show p

    handleActions name network actions0
    debug $ "Initial actions: " ++ show actions0

    proposalTimeout <- randomRIO (800000, 1600000)
    loopResult <- timeout proposalTimeout $ loop state0
    case loopResult of
      Nothing -> do
        debug $ "Proposal timed out - bump and retry"
        -- TODO back off timeout?
        runProposer lock name q (P.succProposalId p) v chan network

      Just Nothing -> do
        info "Learners all learned the value, all done"

      Just (Just newerProposal) -> do
        randomRIO timeoutBounds >>= threadDelay
        runProposer lock name q (P.bumpProposalId p newerProposal) v chan network

  where
    (state0, actions0) = P.startRound q p v
    loop state = tryReadMVar lock >>= \case
      Nothing -> do
        (sender, msg) <- readChan chan
        debug $ "Received message from '" ++ sender ++ "': " ++ show msg
        case msg of
            MsgPromise m -> case P.handlePromise state sender m of

              Left newerProposal -> do
                debug $ "Proposal superseded by " ++ show newerProposal ++ " - abandoning"
                return (Just newerProposal)

              Right (state', actions) -> do
                debug $ "Actions: " ++ show actions
                handleActions name network actions
                loop state'

            _ -> loop state
      _ -> return Nothing

    timeoutBounds = (0, 800000)

    debug = debugM name
    info = infoM name

runAcceptor :: Int -> MessageChannel -> NetworkChannel -> IO ()
runAcceptor i chan network = loop state0
  where
    state0 = A.initialize
    loop state = do
        (sender, msg) <- readChan chan
        debug $ "Received message from '" ++ sender ++ "': " ++ show msg
        case msg of
            MsgPrepare m -> do
                let (state', actions) = A.handlePrepare state sender m
                debug $ "Actions: " ++ show actions
                handleActions name network actions
                loop state'
            MsgAccept m -> do
                let (state', actions) = A.handleAccept state m
                debug $ "Actions: " ++ show actions
                handleActions name network actions
                loop state'
            _ -> loop state

    name = "acceptor" ++ show i
    debug = debugM name

runLearner :: Int -> Quorum -> MessageChannel -> NetworkChannel -> IO Value
runLearner i q chan _network = loop state0
  where
    state0 = L.initialize q
    loop state = do
        (sender, msg) <- readChan chan
        debug $ "Received message from '" ++ sender ++ "': " ++ show msg
        case msg of
            MsgAccepted m -> do
                let state' = L.handleAccepted state sender m
                case L.getValue state' of
                    Nothing -> loop state'
                    Just v -> do
                        info $ "Learned value: " ++ show v
                        return v
            _ -> loop state

    name = "learner" ++ show i
    debug = debugM name
    info = infoM name

runNetwork :: NetworkChannel -> [(String, MessageChannel)] -> MessageChannel -> MessageChannel -> IO ()
runNetwork chan proposers acceptors learners = forever loop
  where
    loop = do
        (sender, action) <- atomically $ readTChan chan
        atomically $ case action of
            Send target message ->
                case lookup target proposers of
                    Nothing -> error $ "Unknown target '" ++ target ++ "'"
                    Just pchan -> writeTChan pchan (sender, message)
            Broadcast group message -> case group of
                                          Acceptors -> writeTChan acceptors (sender, message)
                                          Learners -> writeTChan learners (sender, message)
                                          

main :: IO ()
main = do
    handler <- do
        h <- streamHandler stderr DEBUG
        return $ setFormatter h (simpleLogFormatter "[$loggername] $msg")
    updateGlobalLogger rootLoggerName $
        setLevel DEBUG . setHandlers [handler]

    proposerChans <- replicateM numProposers newTChanIO
    acceptorsChan <- newBroadcastTChanIO
    learnersChan <- newBroadcastTChanIO

    network <- newTChanIO

    let proposers = [("proposer" ++ show i, chan) | (i, chan) <- zip [(0 :: Int) ..] proposerChans]

    networkHandler <- forkIO $ runNetwork network proposers acceptorsChan learnersChan

    learners <- forM [0 .. numLearners - 1] $ \i -> do
                    chan <- atomically $ dupTChan learnersChan
                    async $ runLearner i q chan network

    acceptors <- forM [0 .. numAcceptors - 1] $ \i -> do
                    chan <- atomically $ dupTChan acceptorsChan
                    async $ runAcceptor i chan network

    resultVar <- newEmptyMVar

    proposerAsyncs <- forM proposers $ \(name, chan) -> do
        timeout <- randomRIO (500, 10000)
        threadDelay timeout
        let msg = "Hello world, from " ++ name ++ "!"
        async $ runProposer resultVar name q (P.initialProposalId name) msg chan network

    allResults@(result:_) <- mapM wait learners
    putMVar resultVar result

    mapM_ cancel acceptors
    mapM_ cancel proposerAsyncs
    killThread networkHandler

    putStrLn $ "Learned value: " ++ result
    putStrLn $ "All learned values equal: " ++ show (all (== result) allResults)

  where
    numLearners, numAcceptors, numProposers :: Int
    numLearners = 2
    numAcceptors = 5
    numProposers = 2
    q = quorum $ numAcceptors `div` 2 + 1
