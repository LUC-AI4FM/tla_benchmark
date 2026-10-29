------------------------------ MODULE CheckpointLease ------------------------------
(***************************************************************************)
(* Replicated-state-machine checkpoint coordination with a leader lease.   *)
(*                                                                         *)
(* A set of nodes replicates a shared log.  At most one node at a time may *)
(* hold an effective lease.  Only the lease holder may append, commit,     *)
(* propose a checkpoint (truncation point) or finalize it.  A checkpoint   *)
(* at index i may only be finalized when                                   *)
(*   - i is committed,                                                     *)
(*   - every active replica has acknowledged it holds entries up to i,     *)
(*   - a majority has acknowledged it, and                                 *)
(*   - the finalizer currently holds a valid lease.                        *)
(* Crashed replicas that later recover are caught up by snapshot install.  *)
(* On a leadership change any pending proposal is discarded, and the new  *)
(* leader takes over responsibility for future checkpoints.               *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS
    Node,               \* set of nodes
    MaxLog,             \* bound on log length
    MaxNat,             \* bound on clock / lease expiry values
    NoNode,             \* sentinel: no node
    NoCheckpointLease   \* sentinel: no lease has been granted

VARIABLES
    clock,                \* global logical time
    lease,                \* NoCheckpointLease or [holder |-> n, expiry |-> t]
    leader,               \* node that most recently acquired the lease, or NoNode
    lastIndex,            \* last index of the leader's log
    commitIndex,          \* highest committed index
    matchIndex,           \* matchIndex[n]: prefix of the log stored by n
    active,               \* set of currently up replicas
    proposedIdx,          \* pending checkpoint proposal (0 = none)
    acks,                 \* replicas that acknowledged the pending proposal
    checkpoint,           \* finalized safe truncation point
    finalizedWithoutLease \* ghost: TRUE iff some finalize happened without a lease

vars == << clock, lease, leader, lastIndex, commitIndex, matchIndex, active,
           proposedIdx, acks, checkpoint, finalizedWithoutLease >>

-----------------------------------------------------------------------------
(* Model-checking helpers *)

MCNat == 0..MaxNat

LogIndex == Nat

MCLogIndex == 0..MaxLog

Majority == { Q \in SUBSET Node : 2 * Cardinality(Q) > Cardinality(Node) }

LeaseDuration == 2

Max(a, b) == IF a >= b THEN a ELSE b
Min(a, b) == IF a <= b THEN a ELSE b

NodeSymmetry == Permutations(Node)

-----------------------------------------------------------------------------
(* Lease predicates *)

HasValidLease(n) ==
    /\ lease # NoCheckpointLease
    /\ lease.holder = n
    /\ clock < lease.expiry
    /\ n \in active

NoEffectiveLease ==
    \/ lease = NoCheckpointLease
    \/ clock >= lease.expiry

IsLeader(n) == leader = n /\ HasValidLease(n)

-----------------------------------------------------------------------------
Init ==
    /\ clock = 0
    /\ lease = NoCheckpointLease
    /\ leader = NoNode
    /\ lastIndex = 0
    /\ commitIndex = 0
    /\ matchIndex = [n \in Node |-> 0]
    /\ active = Node
    /\ proposedIdx = 0
    /\ acks = {}
    /\ checkpoint = 0
    /\ finalizedWithoutLease = FALSE

(* Time advances; leases expire as time passes. *)
Tick ==
    /\ clock < MaxNat
    /\ clock' = clock + 1
    /\ UNCHANGED << lease, leader, lastIndex, commitIndex, matchIndex, active,
                    proposedIdx, acks, checkpoint, finalizedWithoutLease >>

(* A node acquires the lease once no lease is effective, with the support *)
(* of an active majority, provided it stores all committed entries.       *)
(* Leadership transfer: pending proposal is discarded, uncommitted        *)
(* suffixes beyond the new leader's log are dropped.                      *)
AcquireLease(n) ==
    /\ n \in active
    /\ NoEffectiveLease
    /\ \E Q \in Majority : Q \subseteq active
    /\ matchIndex[n] >= commitIndex
    /\ clock + LeaseDuration <= MaxNat
    /\ lease' = [holder |-> n, expiry |-> clock + LeaseDuration]
    /\ leader' = n
    /\ lastIndex' = matchIndex[n]
    /\ matchIndex' = [m \in Node |-> Min(matchIndex[m], matchIndex[n])]
    /\ proposedIdx' = 0
    /\ acks' = {}
    /\ UNCHANGED << clock, commitIndex, active, checkpoint, finalizedWithoutLease >>

RenewLease(n) ==
    /\ IsLeader(n)
    /\ clock + LeaseDuration <= MaxNat
    /\ lease' = [lease EXCEPT !.expiry = clock + LeaseDuration]
    /\ UNCHANGED << clock, leader, lastIndex, commitIndex, matchIndex, active,
                    proposedIdx, acks, checkpoint, finalizedWithoutLease >>

Append(n) ==
    /\ IsLeader(n)
    /\ lastIndex < MaxLog
    /\ lastIndex' = lastIndex + 1
    /\ matchIndex' = [matchIndex EXCEPT ![n] = lastIndex + 1]
    /\ UNCHANGED << clock, lease, leader, commitIndex, active,
                    proposedIdx, acks, checkpoint, finalizedWithoutLease >>

(* Leader ships the next entry to a follower, or a snapshot if the follower *)
(* lags behind the truncation point.                                       *)
Replicate(n, m) ==
    /\ IsLeader(n)
    /\ m \in active
    /\ m # n
    /\ matchIndex[m] < lastIndex
    /\ matchIndex' = [matchIndex EXCEPT ![m] =
                         IF matchIndex[m] < checkpoint THEN checkpoint
                                                       ELSE matchIndex[m] + 1]
    /\ UNCHANGED << clock, lease, leader, lastIndex, commitIndex, active,
                    proposedIdx, acks, checkpoint, finalizedWithoutLease >>

Commit(n) ==
    /\ IsLeader(n)
    /\ commitIndex < lastIndex
    /\ \E Q \in Majority : \A q \in Q : matchIndex[q] > commitIndex
    /\ commitIndex' = commitIndex + 1
    /\ UNCHANGED << clock, lease, leader, lastIndex, matchIndex, active,
                    proposedIdx, acks, checkpoint, finalizedWithoutLease >>

Propose(n, i) ==
    /\ IsLeader(n)
    /\ proposedIdx = 0
    /\ i > checkpoint
    /\ i <= commitIndex
    /\ proposedIdx' = i
    /\ acks' = {}
    /\ UNCHANGED << clock, lease, leader, lastIndex, commitIndex, matchIndex,
                    active, checkpoint, finalizedWithoutLease >>

Ack(m) ==
    /\ m \in active
    /\ proposedIdx > 0
    /\ m \notin acks
    /\ matchIndex[m] >= proposedIdx
    /\ acks' = acks \cup {m}
    /\ UNCHANGED << clock, lease, leader, lastIndex, commitIndex, matchIndex,
                    active, proposedIdx, checkpoint, finalizedWithoutLease >>

Finalize(n) ==
    /\ IsLeader(n)
    /\ proposedIdx > 0
    /\ proposedIdx <= commitIndex
    /\ \E Q \in Majority : Q \subseteq acks
    /\ active \subseteq acks
    /\ checkpoint' = proposedIdx
    /\ proposedIdx' = 0
    /\ acks' = {}
    /\ finalizedWithoutLease' = (finalizedWithoutLease \/ ~HasValidLease(n))
    /\ UNCHANGED << clock, lease, leader, lastIndex, commitIndex, matchIndex,
                    active >>

Crash(m) ==
    /\ m \in active
    /\ active' = active \ {m}
    /\ leader' = IF leader = m THEN NoNode ELSE leader
    /\ acks' = acks \ {m}
    /\ UNCHANGED << clock, lease, lastIndex, commitIndex, matchIndex,
                    proposedIdx, checkpoint, finalizedWithoutLease >>

(* A recovering replica installs the current snapshot if it lags. *)
Recover(m) ==
    /\ m \notin active
    /\ active' = active \cup {m}
    /\ matchIndex' = [matchIndex EXCEPT ![m] = Max(matchIndex[m], checkpoint)]
    /\ UNCHANGED << clock, lease, leader, lastIndex, commitIndex,
                    proposedIdx, acks, checkpoint, finalizedWithoutLease >>

Next ==
    \/ Tick
    \/ \E n \in Node :
         \/ AcquireLease(n)
         \/ RenewLease(n)
         \/ Append(n)
         \/ Commit(n)
         \/ Finalize(n)
         \/ Crash(n)
         \/ Recover(n)
         \/ Ack(n)
         \/ \E m \in Node : Replicate(n, m)
         \/ \E i \in 1..MaxLog : Propose(n, i)

Fairness ==
    \A n \in Node :
        /\ WF_vars(RenewLease(n))
        /\ WF_vars(Commit(n))
        /\ WF_vars(Finalize(n))
        /\ WF_vars(Ack(n))
        /\ WF_vars(\E m \in Node : Replicate(n, m))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Invariants *)

TypeInvariant ==
    /\ clock \in Nat
    /\ \/ lease = NoCheckpointLease
       \/ /\ lease.holder \in Node
          /\ lease.expiry \in Nat
    /\ leader \in Node \cup {NoNode}
    /\ lastIndex \in LogIndex
    /\ commitIndex \in LogIndex
    /\ DOMAIN matchIndex = Node
    /\ \A n \in Node : matchIndex[n] \in LogIndex
    /\ active \subseteq Node
    /\ proposedIdx \in LogIndex
    /\ acks \subseteq Node
    /\ checkpoint \in LogIndex
    /\ finalizedWithoutLease \in BOOLEAN

LeaseExclusive ==
    \A n, m \in Node : (HasValidLease(n) /\ HasValidLease(m)) => n = m

LeaseMatchesLeader ==
    \A n \in Node : HasValidLease(n) => leader = n

CommittedPreserved ==
    /\ checkpoint <= commitIndex
    /\ commitIndex <= lastIndex
    /\ \E Q \in Majority : \A q \in Q : matchIndex[q] >= commitIndex

NoNeededEntryDiscarded ==
    \A m \in active : matchIndex[m] >= checkpoint

ProposalWellFormed ==
    proposedIdx > 0 =>
        /\ checkpoint < proposedIdx
        /\ proposedIdx <= commitIndex
        /\ \A a \in acks : matchIndex[a] >= proposedIdx

LeaderLogComplete ==
    leader # NoNode => matchIndex[leader] = lastIndex

CheckpointRespectsLease == finalizedWithoutLease = FALSE

SafetyInvariant ==
    /\ LeaseExclusive
    /\ LeaseMatchesLeader
    /\ CommittedPreserved
    /\ NoNeededEntryDiscarded
    /\ ProposalWellFormed
    /\ LeaderLogComplete
    /\ CheckpointRespectsLease

StateConstraint ==
    /\ clock <= MaxNat
    /\ lastIndex <= MaxLog
    /\ (lease = NoCheckpointLease \/ lease.expiry <= MaxNat)

-----------------------------------------------------------------------------
(* Temporal properties *)

CheckpointMonotonic == [][checkpoint' >= checkpoint]_vars

CommitMonotonic == [][commitIndex' >= commitIndex]_vars

CheckpointProgress ==
    \A i \in 1..MaxLog :
        (proposedIdx = i) ~> (checkpoint >= i \/ proposedIdx # i)

=============================================================================