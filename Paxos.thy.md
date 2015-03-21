# Introduction

Paxos is a distributed consensus algorithm with a rather nice correctness proof of its safety property: the decisions
made by a Paxos cluster will always be consistent even in the face of arbitrary network partitions or delays (although
if the network goes down it will stop making progress).

The file [Paxos.thy](Paxos.thy) contains an Isabelle-checked proof of the safety property of Paxos and related
theorems. This document is a less formal commentary on the proofs.

# Weighted Majority Quorums

First we prove a couple of facts about quorums as defined by weighted majority: if the weighting
function is integer then one of its values can be changed by one unit and every quorum of the new function
intersects every quorum of the old function, and the weights can all be multiplied or divided by constants without
changing the quorum structure.

This will be useful later when looking at managing the topology of a Paxos cluster using consensus within
the cluster, as if the topology changes sufficiently slowly then this can be achieved without having to re-run
the whole algorithm at each change.

# Topology versioning

Next we define the notion of a sequence of topologies, derived from a sequence of values as agreed by a Paxos cluster.
Each topology must consist of pairwise-intersecting, finite, nonempty sets called 'quorums', and moreover quorums from
adjacent pairs of topologies must all pairwise intersect too.

# Single-instance Paxos

Next we prove (following Lamport's method) that any single instance of Paxos remains consistent,
by describing an invariant and showing that this invariant implies consistency.

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

# Multi-Paxos

Next we extend our attention to a sequence of Paxos instances, including the ability for each instance to alter
the topology of subsequent instances. The multi-Paxos invariant is quite similar to the single-Paxos one with an extra
parameter `i` indicating the instance number. Proposals identifiers now carry a topology version number, and instances
have a version number which is defined by the sequence of values agreed by previous instances. Topology versions
must be increasing in the proposal identifiers and instance number respectively.

There are also two properties, `proposed_topology` and `chosen_topology`, relating the topology version number of proposals
to the topology version of each instance: when making a proposal the topology version number must be no
greater than the instance's topology version and when choosing a proposal the proposal must
have a topology version no less than the instance's topology version minus one. That 'minus one' gives the extra wiggle room
needed to allow proposals to be chosen with a slightly-old topology. The condition on each topology to intersect all of
its subsequent topology is used to show that consistency is preserved even given this extra flexibility.

There is also a condition that an instance cannot have a value chosen until the previous instance has been chosen, since without knowing all the previous values we cannot know what the current topology is.

There is one extra message type, `multi_promised`, which is effectively a `promised_free` message for all future instances simultaneously.

Consistency follows from these invariants by showing that each instance satisfies the single-Paxos invariant.

## Preserving invariants

The remainder of the file shows that the empty model (containing no messages) satisfies the
multi-Paxos invariant and shows some conditions
under which an invariant-satisfying model can be modified (by sending a message or updating one of the value functions) into
another invariant-satisfying model. These conditions are designed to be straightforward to verify in an implementation.

### For a proposer:

See lemmas `multiPaxos_change_value_proposed`, `multiPaxos_add_proposal_free` and `multiPaxos_add_proposal_constrained`.

1. If there's a quorum of acceptors `S ∈ QP` that all promised to accept a proposal `p` with no prior value (i.e. `promised_free a p` for all `a ∈ S`) then `p` can be proposed.
2. If there's a quorum of acceptors `S ∈ QP` that all promised to accept a proposal `p` but some of them sent a prior value (i.e. `promised_free a p` or `promised_prev a p` for all `a ∈ S` and `promised_prev a p p'` for some `a ∈ S`) then  `p` can be proposed as long as its value matches the value of the response with the highest identifier.
3. The value of a proposal can be freely changed as long as it has not already been proposed.

### For an acceptor

See lemmas `multiPaxos_change_value_promised`, `multiPaxos_change_value_accepted`, 
`multiPaxos_add_promise_free`, `multiPaxos_add_multi_promise` and `multiPaxos_add_promise_prev`.

1. If an acceptor has accepted no proposals then it may promise to accept anything, with no prior value.
2. If an acceptor has accepted some proposals then it may promise to accept any later proposals, as long as it includes the identifier of the highest proposal it has previously accepted and as long as the values `vP` and `vA` agree where promises are made.
3. An acceptor may accept a proposal as long as it has been proposed, and it hasn't promised to accept later proposals, and the value of `vA` agrees with the value of the proposal itself.
4. An acceptor may freely update `vP` for any proposals for which it has not sent a promise.
5. An acceptor may freely update `vA` for any proposals which it has not accepted.


### For a learner:

See lemma `multiPaxos_add_choice`.

1. If there's a quorum of acceptors `S ∈ QL p` that all accept a proposal `p` then that proposal may be chosen.
2. `QL p` can be freely changed as long as its elements all remain quorums; in particular
  1. extra quorums may be added to `QL p`, and
  2. if `p` can never be chosen then `QL p` can be changed freely.
