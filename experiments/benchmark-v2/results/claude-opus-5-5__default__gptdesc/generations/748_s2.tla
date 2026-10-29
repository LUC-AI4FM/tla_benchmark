------------------------- MODULE MCCheckpointCoordination -------------------------
EXTENDS Naturals, FiniteSets, TLC

\* ---------------------------------------------------------------------------
\* Embedded copy of the checkpoint coordination specification that this
\* module wraps for model checking.
\* ---------------------------------------------------------------------------
------------------------- MODULE CheckpointCoordination -------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS Node, LogIndex, LeaseDuration, Nil

VARIABLES
    leader,        \* the node currently acting as leader (or Nil)
    lease,         \* the shared lease record: [holder, expiry]
    heldUntil,     \* each node's local belief of when its own lease expires
    clock,         \* global logical clock
    openIndices,   \* log indices not yet checkpointed
    checkpointed   \* which node checkpointed each index (or Nil)

vars == <<leader, lease, heldUntil, clock, openIndices, checkpointed>>

Min(S) == CHOOSE x \in S : \A y \in S : x <= y

\* A node believes it holds the lease while the clock is below its expiry.
Holds(n) == clock < heldUntil[n]

TypeOK ==
    /\ leader \in Node \cup {Nil}
    /\ lease \in [holder : Node \cup {Nil}, expiry : Nat]
    /\ heldUntil \in [Node -> Nat]
    /\ clock \in Nat
    /\ openIndices \subseteq LogIndex
    /\ checkpointed \in [LogIndex -> Node \cup {Nil}]

\* The correct lease-replacement predicate: a lease can be taken over only if
\* nobody holds it, it has expired, or the requester already holds it.
CanReplaceLease(n) ==
    \/ lease.holder = Nil
    \/ lease.expiry <= clock
    \/ lease.holder = n

Init ==
    /\ leader = Nil
    /\ lease = [holder |-> Nil, expiry |-> 0]
    /\ heldUntil = [n \in Node |-> 0]
    /\ clock = 0
    /\ openIndices = LogIndex
    /\ checkpointed = [i \in LogIndex |-> Nil]

Tick ==
    /\ clock' = clock + 1
    /\ UNCHANGED <<leader, lease, heldUntil, openIndices, checkpointed>>

BecomeLeader(n) ==
    /\ leader # n
    /\ leader' = n
    /\ UNCHANGED <<lease, heldUntil, clock, openIndices, checkpointed>>

\* Lease acquisition parameterized by the replacement predicate.
AcquireLeaseWith(n, Pred(_)) ==
    /\ Pred(n)
    /\ lease' = [holder |-> n, expiry |-> clock + LeaseDuration]
    /\ heldUntil' = [heldUntil EXCEPT ![n] = clock + LeaseDuration]
    /\ UNCHANGED <<leader, clock, openIndices, checkpointed>>

AcquireLease(n) == AcquireLeaseWith(n, CanReplaceLease)

Checkpoint(n) ==
    /\ Holds(n)
    /\ openIndices # {}
    /\ LET i == Min(openIndices) IN
         /\ checkpointed' = [checkpointed EXCEPT ![i] = n]
         /\ openIndices' = openIndices \ {i}
    /\ UNCHANGED <<leader, lease, heldUntil, clock>>

Next ==
    \/ Tick
    \/ \E n \in Node : BecomeLeader(n)
    \/ \E n \in Node : AcquireLease(n)
    \/ \E n \in Node : Checkpoint(n)

Spec == Init /\ [][Next]_vars

\* Safety: at most one node believes it holds the lease at any time.
LeaseMutualExclusion ==
    \A n, m \in Node : (n # m) => ~(Holds(n) /\ Holds(m))

\* Safety: a node that believes it holds the lease is the recorded holder.
LeaseConsistency ==
    \A n \in Node : Holds(n) => lease.holder = n
================================================================================