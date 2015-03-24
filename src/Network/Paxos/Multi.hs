{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE LambdaCase #-}

module Network.Paxos.Multi where

import Network.Paxos.Multi.Proposer
import Network.Paxos.Multi.Acceptor
import Network.Paxos.Multi.Learner

