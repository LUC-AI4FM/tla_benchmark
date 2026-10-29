------------------------- MODULE CheckpointCoordination -------------------------
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS
    Node,               \* set of nodes participating in the replicated log
    MaxLog,             \* bound on the log length (for model checking)
    MaxNat,             \* bound on naturals (for model checking)
    NoNode,             \* sentinel: no node
    NoCheckpointLease   \* sentinel: no checkpoint lease is held

ASSUME MaxLog \in Nat /\ MaxLog >= 1
ASSUME MaxNat \in Nat /\ MaxNat >= MaxLog
ASSUME NoNode \notin Node

VARIABLES
    leader,       \* current leader node
    logLen,       \* index of the last entry in the leader's log
    commitIndex,  \* highest committed log index
    matchIndex,   \* matchIndex[n]: highest log index replicated at node n
    truncIndex,   \* log entries 1..truncIndex have been compacted away
    checkpoint,   \* checkpoint[n]: index covered by node n's latest checkpoint
    lease         \* current checkpoint lease, or NoCheckpointLease

vars == <<leader, logLen, commitIndex, matchIndex, truncIndex, checkpoint, lease>>

-----------------------------------------------------------------------------
\* Model-checking helpers

MCNat == 0..MaxNat

LogIndex == Nat \ {0}

MCLogIndex == 1..MaxLog

Majority == { Q \in SUBSET Node : 2 * Cardinality(Q) > Cardinality(Node) }

NodeSymmetry == Permutations(Node)

Min(a, b) == IF a <= b THEN a ELSE b

Lease == [node : Node, index : LogIndex]

\* Indices of the log that are still "open", i.e. not compacted away.
OpenIndices == { i \in LogIndex : i > truncIndex }

-----------------------------------------------------------------------------
\* Lease replacement logic.
\* A new lease requested by node n may replace the existing one only if there
\* is no lease, or the existing lease is held by n itself (it is renewing it
\* for a newer index). The tempting optimization
\*     \/ lease.node = leader
\* is NOT considered safe: it would let a leader's in-progress checkpoint be
\* silently stolen by another node.
ShouldReplaceLease(n) ==
    \/ lease = NoCheckpointLease
    \/ lease.node = n

-----------------------------------------------------------------------------
Init ==
    /\ leader \in Node
    /\ logLen = 0
    /\ commitIndex = 0
    /\ matchIndex = [n \in Node |-> 0]
    /\ truncIndex = 0
    /\ checkpoint = [n \in Node |-> 0]
    /\ lease = NoCheckpointLease

\* The leader appends a new entry to the log.
AppendEntry ==
    /\ logLen < MaxLog
    /\ logLen' = logLen + 1
    /\ matchIndex' = [matchIndex EXCEPT ![leader] = logLen + 1]
    /\ UNCHANGED <<leader, commitIndex, truncIndex, checkpoint, lease>>

\* A follower receives the next log entry (only if it is not compacted).
Replicate(n) ==
    /\ n /= leader
    /\ matchIndex[n] < logLen
    /\ matchIndex[n] >= truncIndex
    /\ matchIndex' = [matchIndex EXCEPT ![n] = matchIndex[n] + 1]
    /\ UNCHANGED <<leader, logLen, commitIndex, truncIndex, checkpoint, lease>>

\* A lagging follower whose next entry was compacted installs a checkpoint.
InstallCheckpoint(n) ==
    /\ n /= leader
    /\ matchIndex[n] < truncIndex
    /\ \E m \in Node :
          /\ checkpoint[m] >= truncIndex
          /\ matchIndex' = [matchIndex EXCEPT ![n] = checkpoint[m]]
          /\ checkpoint' = [checkpoint EXCEPT ![n] = checkpoint[m]]
    /\ UNCHANGED <<leader, logLen, commitIndex, truncIndex, lease>>

\* The leader advances the commit index once a majority has replicated.
AdvanceCommit ==
    /\ \E i \in (commitIndex + 1)..logLen :
          /\ \E Q \in Majority : \A m \in Q : matchIndex[m] >= i
          /\ commitIndex' = i
    /\ UNCHANGED <<leader, logLen, matchIndex, truncIndex, checkpoint, lease>>

\* Node n acquires (or renews) the checkpoint lease for index i.
AcquireLease(n, i) ==
    /\ i \in LogIndex
    /\ i <= commitIndex
    /\ i <= matchIndex[n]
    /\ i > checkpoint[n]
    /\ ShouldReplaceLease(n)
    /\ lease' = [node |-> n, index |-> i]
    /\ UNCHANGED <<leader, logLen, commitIndex, matchIndex, truncIndex, checkpoint>>

\* The lease holder finishes its checkpoint and releases the lease.
CompleteCheckpoint ==
    /\ lease /= NoCheckpointLease
    /\ lease.index <= matchIndex[lease.node]
    /\ checkpoint' = [checkpoint EXCEPT ![lease.node] = lease.index]
    /\ lease' = NoCheckpointLease
    /\ UNCHANGED <<leader, logLen, commitIndex, matchIndex, truncIndex>>

\* The lease holder abandons its checkpoint.
ReleaseLease ==
    /\ lease /= NoCheckpointLease
    /\ lease' = NoCheckpointLease
    /\ UNCHANGED <<leader, logLen, commitIndex, matchIndex, truncIndex, checkpoint>>

\* The leader compacts the log up to i, covered by some checkpoint.
\* At least one log index always remains open.
Truncate(i) ==
    /\ i > truncIndex
    /\ i <= commitIndex
    /\ i < logLen
    /\ \E m \in Node : checkpoint[m] >= i
    /\ truncIndex' = i
    /\ UNCHANGED <<leader, logLen, commitIndex, matchIndex, checkpoint, lease>>

\* A node that holds all committed entries becomes the new leader.
ElectLeader(n) ==
    /\ n /= leader
    /\ matchIndex[n] >= commitIndex
    /\ matchIndex[n] > truncIndex
    /\ leader' = n
    /\ logLen' = matchIndex[n]
    /\ matchIndex' = [m \in Node |-> Min(matchIndex[m], matchIndex[n])]
    /\ UNCHANGED <<commitIndex, truncIndex, checkpoint, lease>>

Next ==
    \/ AppendEntry
    \/ AdvanceCommit
    \/ CompleteCheckpoint
    \/ ReleaseLease
    \/ \E n \in Node : Replicate(n) \/ InstallCheckpoint(n) \/ ElectLeader(n)
    \/ \E n \in Node, i \in LogIndex : AcquireLease(n, i)
    \/ \E i \in LogIndex : Truncate(i)

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
TypeInvariant ==
    /\ leader \in Node
    /\ logLen \in Nat
    /\ commitIndex \in Nat
    /\ matchIndex \in [Node -> Nat]
    /\ truncIndex \in Nat
    /\ checkpoint \in [Node -> Nat]
    /\ lease \in Lease \cup {NoCheckpointLease}

\* Progress: some log indices are always left open.
OpenIndicesExist == OpenIndices /= {}

SafetyInvariant ==
    /\ OpenIndicesExist
    /\ truncIndex <= commitIndex
    /\ commitIndex <= logLen
    /\ matchIndex[leader] = logLen
    /\ \A n \in Node : checkpoint[n] <= matchIndex[n]
    /\ \A n \in Node : checkpoint[n] <= commitIndex
    \* compacted data is always recoverable from some checkpoint
    /\ truncIndex > 0 => \E m \in Node : checkpoint[m] >= truncIndex
    \* a committed entry is held by a majority of nodes
    /\ \E Q \in Majority : \A m \in Q : matchIndex[m] >= commitIndex
    \* the lease always refers to a committed index held by its owner
    /\ lease /= NoCheckpointLease =>
          /\ lease.index <= commitIndex
          /\ lease.index <= matchIndex[lease.node]

StateConstraint ==
    /\ logLen <= MaxLog
    /\ commitIndex <= MaxNat
    /\ truncIndex <= MaxNat
=============================================================================