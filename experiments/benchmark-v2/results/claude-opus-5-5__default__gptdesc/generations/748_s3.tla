---------------------------- MODULE MCCheckpointCoordination ----------------------------
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS
    Node,
    MaxNat,
    MaxLogIndex,
    LeaseDuration

ASSUME Node # {} /\ IsFiniteSet(Node)
ASSUME MaxNat \in Nat /\ MaxNat > 0
ASSUME MaxLogIndex \in Nat /\ MaxLogIndex > 0
ASSUME LeaseDuration \in Nat /\ LeaseDuration > 0

NoNode == CHOOSE x : x \notin Node

(***************************************************************************)
(* Bounded ranges that override the unbounded Nat and log-index domains.   *)
(***************************************************************************)
MCNat == 0 .. MaxNat
MCLogIndex == 1 .. MaxLogIndex

Min(a, b) == IF a <= b THEN a ELSE b

VARIABLES
    Leader,
    LogLength,
    CurrentTime,
    Lease,
    Checkpointing,
    LastCheckpoint

vars == <<Leader, LogLength, CurrentTime, Lease, Checkpointing, LastCheckpoint>>

LeaseRecord == [holder : Node \cup {NoNode}, expiry : MCNat]

ReleasedLease == [holder |-> NoNode, expiry |-> 0]

TypeOK ==
    /\ Leader \in Node
    /\ LogLength \in 0 .. MaxLogIndex
    /\ CurrentTime \in MCNat
    /\ Lease \in LeaseRecord
    /\ Checkpointing \in [Node -> BOOLEAN]
    /\ LastCheckpoint \in 0 .. MaxLogIndex

OpenIndices == {i \in MCLogIndex : i > LogLength}

LeaseExpired == Lease.expiry < CurrentTime

(***************************************************************************)
(* Correct lease-replacement predicate of the coordination specification.  *)
(***************************************************************************)
IsLeaseReplaceable ==
    \/ Lease.holder = NoNode
    \/ LeaseExpired

(***************************************************************************)
(* Bad optimization: also allow replacing the lease whenever it is held by *)
(* the current leader. This is intentionally incorrect.                    *)
(***************************************************************************)
BadIsLeaseReplaceable ==
    \/ IsLeaseReplaceable
    \/ Lease.holder = Leader

-----------------------------------------------------------------------------

Init ==
    /\ Leader \in Node
    /\ LogLength = 0
    /\ CurrentTime = 0
    /\ Lease = ReleasedLease
    /\ Checkpointing = [n \in Node |-> FALSE]
    /\ LastCheckpoint = 0

Tick ==
    /\ CurrentTime < MaxNat
    /\ CurrentTime' = CurrentTime + 1
    /\ Checkpointing' =
         [n \in Node |->
            Checkpointing[n] /\ ~(Lease.holder = n /\ Lease.expiry < CurrentTime + 1)]
    /\ UNCHANGED <<Leader, LogLength, Lease, LastCheckpoint>>

ElectLeader(n) ==
    /\ n # Leader
    /\ Leader' = n
    /\ UNCHANGED <<LogLength, CurrentTime, Lease, Checkpointing, LastCheckpoint>>

AppendEntry ==
    /\ LogLength < MaxLogIndex
    /\ LogLength' = LogLength + 1
    /\ UNCHANGED <<Leader, CurrentTime, Lease, Checkpointing, LastCheckpoint>>

AcquireLease(n, Replaceable) ==
    /\ n # Leader
    /\ Replaceable
    /\ Lease' = [holder |-> n,
                 expiry |-> Min(CurrentTime + LeaseDuration, MaxNat)]
    /\ UNCHANGED <<Leader, LogLength, CurrentTime, Checkpointing, LastCheckpoint>>

StartCheckpoint(n) ==
    /\ Lease.holder = n
    /\ ~LeaseExpired
    /\ ~Checkpointing[n]
    /\ Checkpointing' = [Checkpointing EXCEPT ![n] = TRUE]
    /\ UNCHANGED <<Leader, LogLength, CurrentTime, Lease, LastCheckpoint>>

FinishCheckpoint(n) ==
    /\ Checkpointing[n]
    /\ Lease.holder = n
    /\ ~LeaseExpired
    /\ LastCheckpoint' = LogLength
    /\ Checkpointing' = [Checkpointing EXCEPT ![n] = FALSE]
    /\ Lease' = ReleasedLease
    /\ UNCHANGED <<Leader, LogLength, CurrentTime>>

NextWith(Replaceable) ==
    \/ Tick
    \/ AppendEntry
    \/ \E n \in Node :
         \/ ElectLeader(n)
         \/ AcquireLease(n, Replaceable)
         \/ StartCheckpoint(n)
         \/ FinishCheckpoint(n)

Next == NextWith(IsLeaseReplaceable)

BadNext == NextWith(BadIsLeaseReplaceable)

Spec == Init /\ [][Next]_vars

BadSpec == Init /\ [][BadNext]_vars

-----------------------------------------------------------------------------
(***************************************************************************)
(* Model-checking constraints and symmetry.                                *)
(***************************************************************************)
StateConstraint ==
    /\ OpenIndices # {}
    /\ CurrentTime \in MCNat

Symmetry == Permutations(Node)

-----------------------------------------------------------------------------
(***************************************************************************)
(* Safety invariants.                                                      *)
(***************************************************************************)
NoConcurrentCheckpoints ==
    \A m, n \in Node : (Checkpointing[m] /\ Checkpointing[n]) => m = n

CheckpointerHoldsLease ==
    \A n \in Node : Checkpointing[n] => Lease.holder = n

CheckpointWithinLog == LastCheckpoint <= LogLength

Safety ==
    /\ TypeOK
    /\ NoConcurrentCheckpoints
    /\ CheckpointerHoldsLease
    /\ CheckpointWithinLog

THEOREM Spec => []Safety
=============================================================================