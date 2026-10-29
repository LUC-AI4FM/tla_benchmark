---------------------------- MODULE MCCheckpointCoordination ----------------------------
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS
    Node,
    Majority,
    MaxLog,
    MaxNat,
    NoNode,
    NoCheckpointLease

VARIABLES
    Clock,
    Leader,
    Log,
    AppliedIndex,
    CurrentLease,
    IsCheckpointing

vars == <<Clock, Leader, Log, AppliedIndex, CurrentLease, IsCheckpointing>>

----------------------------------------------------------------------------
\* Bounded overrides for model checking

LogIndex == Nat \ {0}

MCLogIndex == 1 .. MaxLog

MCNat == 0 .. MaxNat

----------------------------------------------------------------------------
\* Helper definitions

LeaseDuration == 2

Lease == [node : Node, expiration : Nat]

OpenEntry == [type |-> "Open"]

LeaseEntry == [type : {"Lease"}, lease : Lease]

LogEntry == {OpenEntry} \cup LeaseEntry

OpenIndices == {i \in LogIndex : Log[i].type = "Open"}

NextIndex ==
    CHOOSE i \in OpenIndices : \A j \in OpenIndices : i <= j

IsLeader(n) == Leader # NoNode /\ Leader = n

ShouldReplaceLease(lease) ==
    \/ lease = NoCheckpointLease
    \/ lease.expiration <= Clock

\* Incorrect optimization: also replace lease whenever the current leader holds it
IncorrectShouldReplaceLease(lease) ==
    \/ ShouldReplaceLease(lease)
    \/ /\ lease # NoCheckpointLease
       /\ Leader # NoNode
       /\ lease.node = Leader

----------------------------------------------------------------------------
\* Initial state

Init ==
    /\ Clock = 0
    /\ Leader = NoNode
    /\ Log = [i \in LogIndex |-> OpenEntry]
    /\ AppliedIndex = [n \in Node |-> 0]
    /\ CurrentLease = [n \in Node |-> NoCheckpointLease]
    /\ IsCheckpointing = [n \in Node |-> FALSE]

----------------------------------------------------------------------------
\* Actions

\* Time advances; nodes whose lease expires must abort checkpointing
Tick ==
    /\ Clock + 1 \in Nat
    /\ Clock' = Clock + 1
    /\ IsCheckpointing' =
        [n \in Node |->
            /\ IsCheckpointing[n]
            /\ CurrentLease[n] # NoCheckpointLease
            /\ Clock + 1 < CurrentLease[n].expiration]
    /\ UNCHANGED <<Leader, Log, AppliedIndex, CurrentLease>>

\* A non-checkpointing, fully caught-up node becomes leader
ElectLeader(n) ==
    /\ ~IsLeader(n)
    /\ ~IsCheckpointing[n]
    /\ OpenIndices # {}
    /\ AppliedIndex[n] = NextIndex - 1
    /\ Leader' = n
    /\ UNCHANGED <<Clock, Log, AppliedIndex, CurrentLease, IsCheckpointing>>

\* The current leader fails or steps down
LeaderFails ==
    /\ Leader # NoNode
    /\ Leader' = NoNode
    /\ UNCHANGED <<Clock, Log, AppliedIndex, CurrentLease, IsCheckpointing>>

\* The leader replicates (via quorum) a new checkpoint lease for some follower
GrantLease(m) ==
    /\ Leader # NoNode
    /\ m # Leader
    /\ OpenIndices # {}
    /\ AppliedIndex[Leader] = NextIndex - 1
    /\ ShouldReplaceLease(CurrentLease[Leader])
    /\ Clock + LeaseDuration \in Nat
    /\ Log' = [Log EXCEPT ![NextIndex] =
                [type |-> "Lease",
                 lease |-> [node |-> m, expiration |-> Clock + LeaseDuration]]]
    /\ UNCHANGED <<Clock, Leader, AppliedIndex, CurrentLease, IsCheckpointing>>

\* A node applies the next committed log entry
ApplyEntry(n) ==
    LET i == AppliedIndex[n] + 1 IN
    /\ i \in LogIndex
    /\ Log[i].type = "Lease"
    /\ AppliedIndex' = [AppliedIndex EXCEPT ![n] = i]
    /\ CurrentLease' = [CurrentLease EXCEPT ![n] = Log[i].lease]
    /\ UNCHANGED <<Clock, Leader, Log, IsCheckpointing>>

\* A node holding an unexpired lease starts checkpointing
StartCheckpoint(n) ==
    /\ ~IsLeader(n)
    /\ ~IsCheckpointing[n]
    /\ CurrentLease[n] # NoCheckpointLease
    /\ CurrentLease[n].node = n
    /\ Clock < CurrentLease[n].expiration
    /\ IsCheckpointing' = [IsCheckpointing EXCEPT ![n] = TRUE]
    /\ UNCHANGED <<Clock, Leader, Log, AppliedIndex, CurrentLease>>

\* A node finishes its checkpoint
FinishCheckpoint(n) ==
    /\ IsCheckpointing[n]
    /\ IsCheckpointing' = [IsCheckpointing EXCEPT ![n] = FALSE]
    /\ UNCHANGED <<Clock, Leader, Log, AppliedIndex, CurrentLease>>

Next ==
    \/ Tick
    \/ LeaderFails
    \/ \E n \in Node :
        \/ ElectLeader(n)
        \/ GrantLease(n)
        \/ ApplyEntry(n)
        \/ StartCheckpoint(n)
        \/ FinishCheckpoint(n)

Spec == Init /\ [][Next]_vars

----------------------------------------------------------------------------
\* Invariants

TypeInvariant ==
    /\ Clock \in Nat
    /\ Leader \in Node \cup {NoNode}
    /\ Log \in [LogIndex -> LogEntry]
    /\ AppliedIndex \in [Node -> Nat]
    /\ CurrentLease \in [Node -> Lease \cup {NoCheckpointLease}]
    /\ IsCheckpointing \in [Node -> BOOLEAN]

SafetyInvariant ==
    /\ \A n, m \in Node :
        (IsCheckpointing[n] /\ IsCheckpointing[m]) => n = m
    /\ Leader # NoNode => ~IsCheckpointing[Leader]
    /\ Cardinality({n \in Node : ~IsCheckpointing[n]}) >= Majority

----------------------------------------------------------------------------
\* Model-checking configuration helpers

StateConstraint == OpenIndices # {}

NodeSymmetry == Permutations(Node)

=============================================================================