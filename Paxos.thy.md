# Safety proof

The file [Paxos.thy](Paxos.thy) contains an Isabelle-checked proof of the safety property of Paxos. Less formally:

Let 
- `pid` be the type of proposal identifiers,
- `acc` the type of acceptors,
- `val` the type of values of proposals,
- `<` be an ordering on `pid` which is transitive, wellfounded and total,
- `QP` and `QL` be collections of finite subsets of `acc` such that
  - every member of `QP` intersects every member of `QL`,
  - every member of `QP` is finite,
  - `QP` is nonempty
- `promised` be a ternary relation on `acc * pid * Maybe pid`,
- `accepted` be a binary relation on `acc * pid`, and
- `proposed` and `chosen` be sets of proposal identifiers,
- `v` be a function `pid -> val`, and
- `vP` and `vA` be functions `acc -> pid -> val`.

Intuitively, `QP` and `QL` are the collections of quorums from the Proposers' and Learners' points of view respectively. (`QP` and `QL` may differ to allow the membership of the group of acceptors to change). The predicates `promised`, `proposed`, `accepted` and `chosen` represent the messages that have been sent (but not necessarily received or processed by all other agents). The function `v` gives the values of proposals which have been proposed, and `vP` (resp. `vA`) gives the values of proposals that each acceptor has promised (resp. accepted).

Given the following invariants:

- If `chosen p` then there exists a quorum `S ∈ QL` such that if `a ∈ S` then `accepted a p`.
- If `proposed p` then there exists a quorum `S ∈ QP` such that if `a ∈ S` then `promised a p _`, and either
  - `promised a p Nothing` for all `a ∈ S`, or
  - for each `a1 ∈ S` with `promised a1 p (Just p1)`, either
    - `v p == vP a1 p`, or
    - there is an `a2 ∈ S` with `promised a2 p (Just p2)` and `p1 < p2`.
- If `accepted a p` then `proposed p`.
- If `accepted a p` then `v p == vA a p`.
- If `promised a p0 (Just p1)` then `accepted a p1`.
- If `promised a p0 (Just p1)` then `p1 < p0`.
- If `promised a p0 (Just p1)` and `accepted a p2` and `p2 < p0` then either
  - `p1 == p2` and `vP p0 == vA p1`, or
  - `p2 < p1`
- If `promised a p0 Nothing` and `accepted a p1` then `p0 < p1` or `p0 == p1`.

Then any two chosen propositions `p1` and `p2` have `v p1 == v p2`. This is theorem `paxos_consistent` in the theory file.

This is the heart of the safety proof for Paxos. The predicates `promised`, `proposed` and `accepted` correspond to messages that may be sent. Pretty remarkable.

Interestingly, there's no need to consider the passage of time or similar, which is how it remains safe even given arbitrary message loss, delay, and reordering. The model is in terms of some kind of platonic whole-system state - no single agent can know the whole state.

Of course, other messages can be sent without affecting this safety proof - in particular, you need to pass the actual values around somehow, and hold leadership elections and send negative acknowledgements and so on, and actually get the acceptors to promise things by sending the initial `prepare` message which is also notably absent here.

The first invariant is for the Learner agents to satisfy. They do so by collecting `accepted` messages until they see an agreeing quorum. Note that they don't need to look at just the latest `accepted` message for each acceptor: the protocol remains safe if messages are lost.

The second invariant is for the Proposer agent to satisfy. It does so by collecting `promised` messages until it has an agreeing quorum. The quorum it collects may determine the `value` of the proposition (second disjunct); if it does not (first disjunct) then the Proposer may freely choose its value without breaking this invariant.

The remaining five invariants are the responsibility of the Acceptor agents, and can be satisfied by tracking simply the greatest promosed id and the greatest accepted id.
