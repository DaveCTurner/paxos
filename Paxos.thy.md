# Safety proof

The file [Paxos.thy](Paxos.thy) contains an Isabelle-checked proof of the safety property of Paxos. Less formally:

Let 
- `pid` be the type of proposal identifiers,
- `acc` the type of acceptors,
- `val` the type of values of proposals,
- `<` be an ordering on `pid` which is transitive, wellfounded and total,
- `QP` be a nonempty collection of finite subsets of `acc`,
- `QL` be a function `pid -> Powerset(acc)` such that for every proposal `p` every member of `QP` intersects every member of `QL p`,
- `promised_free` be a binary relation on `acc * pid`,
- `promised_prev` be a ternary relation on `acc * pid * pid`,
- `accepted` be a binary relation on `acc * pid`, and
- `proposed` and `chosen` be sets of proposal identifiers,
- `v` be a function `pid -> val`, and
- `vP` and `vA` be functions `acc -> pid -> val`.

Intuitively, `QP` and `QL p` are the collections of quorums from the Proposers' and Learners' points of view respectively. (`QP` and `QL p` are typically equal but are permitted to vary like this to support changing the membership of the group of acceptors whilst remaining consistent). The function `v` gives the values of proposals which have been proposed, and `vP` (resp. `vA`) gives the values of proposals that each acceptor has promised (resp. accepted). The predicates `promised_free`, `promised_prev`, `proposed`, `accepted` and `chosen` represent the messages that have been sent (but not necessarily received or processed by all other agents):
- `promised_free a p` indicates that acceptor `a` promises to accept no proposals numbered below `p`, and that it has not yet accepted any proposal.
- `promised_prev a p p'` indicates that acceptor `a` promises to accept no proposals numbered below `p`, and that it accepted proposal `p'` but has accepted no later one.
- `proposed p` indicates that proposal `p` has been made by some proposer.
- `accepted a p` indicates that acceptor `a` accepts proposal `p`.
- `chosen p` indicates that proposal `p` has been chosen by some learner.

Given the following invariants:

- If `chosen p` then there exists a quorum `S ∈ QL p` such that if `a ∈ S` then `accepted a p`.
- If `proposed p` then there exists a quorum `S ∈ QP` such that if `a ∈ S` then `promised_free a p` or `promised_prev a p _`, and either
  - `promised_free a p Nothing` for all `a ∈ S`, or
  - for each `a1 ∈ S` with `promised_prev a1 p p1`, either
    - `v p == vP a1 p`, or
    - there is an `a2 ∈ S` with `promised_prev a2 p p2` and `p1 < p2`.
- If `accepted a p` then `proposed p`.
- If `accepted a p` then `v p == vA a p`.
- If `promised_prev a p0 p1` then `accepted a p1`.
- If `promised_prev a p0 p1` then `p1 < p0`.
- If `promised_prev a p0 p1` and `accepted a p2` and `p2 < p0` then either
  - `p1 == p2` and `vP p0 == vA p1`, or
  - `p2 < p1`
- If `promised_free a p0` and `accepted a p1` then `p0 < p1` or `p0 == p1`.

Then any two chosen propositions `p1` and `p2` have `v p1 == v p2`. This is theorem `paxos_consistent` in the theory file.

This is the heart of the safety proof for Paxos. The predicates `promised_free`, `promised_prev`, `proposed` and `accepted` correspond to messages that may be sent. Pretty remarkable.

Interestingly, there's no need to consider the passage of time or similar, which is how it remains safe even given arbitrary message loss, delay, and reordering. The model is in terms of some kind of platonic whole-system state - no single agent can know the whole state.

Of course, other messages can be sent without affecting this safety proof - in particular, you need to pass the actual values around somehow, and hold leadership elections and send negative acknowledgements and so on, and actually get the acceptors to promise things by sending the initial `prepare` message which is also notably absent here.

## Preserving invariants

The remainder of the file shows that the empty model (containing no messages) is safe and shows some conditions under which a safe model can be modified (by sending a message or updating one of the value functions) into another safe model: 

### For a proposer:

1. If there's a quorum of acceptors `S ∈ QP` that all promised to accept a proposal `p` with no prior value (i.e. `promised_free a p` for all `a ∈ S`) then `p` can be proposed.
2. If there's a quorum of acceptors `S ∈ QP` that all promised to accept a proposal `p` but some of them sent a prior value (i.e. `promised_free a p` or `promised_prev a p` for all `a ∈ S` and `promised_prev a p p'` for some `a ∈ S`) then  `p` can be proposed as long as its value matches the value of the response with the highest identifier.
3. The value of a proposal can be freely changed as long as it has not already been proposed.

### For a learner:

1. If there's a quorum of acceptors `S ∈ QL p` that all accept a proposal `p` then that proposal may be chosen.
2. `QL p` can be freely changed as long as its elements all remain quorums; in particular
  1. extra quorums may be added to `QL p`, and
  2. if `p` can never be chosen then `QL p` can be changed freely.

### For an acceptor

1. If an acceptor has accepted no proposals then it may promise to accept anything, with no prior value.
2. If an acceptor has accepted some proposals then it may promise to accept any later proposals, as long as it includes the identifier of the highest proposal it has previously accepted and as long as the values `vP` and `vA` agree where promises are made.
3. An acceptor may accept a proposal as long as it has been proposed, and it hasn't promised to accept later proposals, and the value of `vA` agrees with the value of the proposal itself.
4. An acceptor may freely update `vP` for any proposals for which it has not sent a promise.
5. An acceptor may freely update `vA` for any proposals which it has not accepted.
