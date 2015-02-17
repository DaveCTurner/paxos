# Safety proof

The file `Paxos.thy` contains an Isabelle-checked proof of the safety property of Paxos. Less formally:

Let 
- `pid` be the type of proposal identifiers and `acc` the type of acceptors,
- `<` be an ordering on `pid` which is transitive, wellfounded, and total,
- `Q` be a collection of finite subsets of `acc` which pairwise intersect (an element of `Q` is a quorum of acceptors),
- `promised` be a ternary relation on `acc * pid * Maybe pid`,
- `accepted` be a binary relation on `acc * pid`, and
- `proposed` and `chosen` be sets of proposal identifiers,
- `value` a function `pid -> v` where `v` is the type of values of propositions.

Given the following invariants:

- If `chosen p` then there exists a quorum `S` such that if `a ∈ S` then `accepted a p`.
- If `proposed p` then there exists a quorum `S` such that if `a ∈ S` then `promised a p _`, and either
  - `promised a p Nothing` for all `a ∈ S`, or
  - for each `a1 ∈ S` with `promised a1 p (Just p1)`, either
    - `value p == value p1`, or
    - there is an `a2 ∈ S` with `promised a2 p (Just p2)` and `p1 < p2`.
- If `accepted a p` then `proposed p`.
- If `promised a p0 (Just p1)` then `accepted a p1`.
- If `promised a p0 (Just p1)` then `p1 < p0`.
- If `promised a p0 (Just p1)` and `accepted a p2` and `p2 < p0` then either
  - `p1 == p2` and `value p1 == value p0`, or
  - `p2 < p1`
- If `promised a p0 Nothing` and `accepted a p1` then `p0 < p1` or `p0 == p1`.

Then any two chosen propositions have equal `value`.

This is the heart of the safety proof for Paxos. The predicates `promised`, `proposed` and `accepted` correspond to messages that may be sent. Pretty remarkable.

Interestingly, there's no need to consider the passage of time or similar, which is how it remains safe even given arbitrary message loss, delay, and reordering. The model is in terms of some kind of platonic whole-system state - no single agent can know the whole state.

Of course, other messages can be sent without affecting this safety proof - in particular, you need to pass the actual values around somehow, and hold leadership elections and send negative acknowledgements and so on, and actually get the acceptors to promise things by sending the initial `prepare` message which is also notably absent here.

The first invariant is for the Learner agents to satisfy. They do so by collecting `accepted` messages until they see an agreeing quorum. Note that they don't need to look at just the latest `accepted` message for each acceptor: the protocol remains safe if messages are lost.

The second invariant is for the Proposer agent to satisfy. It does so by collecting `promised` messages until it has an agreeing quorum. The quorum it collects may determine the `value` of the proposition (second disjunct); if it does not (first disjunct) then the Proposer may freely choose its value without breaking this invariant.

The remaining five invariants are the responsibility of the Acceptor agents, and can be satisfied by tracking simply the greatest promosed id and the greatest accepted id.
