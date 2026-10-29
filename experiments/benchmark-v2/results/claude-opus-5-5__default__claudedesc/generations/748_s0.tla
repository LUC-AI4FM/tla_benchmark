------------------------- MODULE MCCheckpointCoordination -------------------------
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS
    n1, n2, n3,     \* the three nodes
    NoNode,         \* model value denoting "no node"
    MaxLog,         \* bound on log indices
    MaxNat          \* bound on natural numbers

ASSUME MaxLog \in Nat /\ MaxLog >= 1
ASSUME MaxNat \in Nat
ASSUME NoNode \notin {n1, n2, n3}

Node == {n1, n2, n3}

Majority == 2

Quorums == {Q \in SUBSET Node : Cardinality(Q) >= Majority}

LogIndex == 1 .. MaxLog
NatBound == 0 .. MaxNat

LeaseDuration == 2

Min(a, b) == IF a <= b THEN a ELSE b

Entry == [type : {"Lease", "Op"}, node : Node \cup {NoNode}, expiration : NatBound]

NoLease == [type |-> "Lease", node |-> NoNode, expiration |-> 0]

VARIABLES
    IsNodeUp,            \* whether each node is up
    Leader,              \* current leader
    ReplicatedLog,       \* the replicated log
    ExecutionCounter,    \* number of log entries executed by each node
    IsTakingCheckpoint,  \* whether each node is currently checkpointing
    LatestCheckpoint,    \* log index covered by each node's latest checkpoint
    Clock                \* bounded global time

vars == << IsNodeUp, Leader, ReplicatedLog, ExecutionCounter,
           IsTakingCheckpoint, LatestCheckpoint, Clock >>

-----------------------------------------------------------------------------------

OpenIndices == {i \in LogIndex : i > Len(ReplicatedLog)}

\* Most recent lease in the prefix of the log executed by node n.
CurrentLease(n) ==
    LET idx == {i \in 1 .. ExecutionCounter[n] : ReplicatedLog[i].type = "Lease"}
    IN IF idx = {}
       THEN NoLease
       ELSE ReplicatedLog[CHOOSE i \in idx : \A j \in idx : j <= i]

LeaseValid(lease, t) == lease.node # NoNode /\ t <= lease.expiration

HasLease(n) ==
    /\ CurrentLease(n).node = n
    /\ LeaseValid(CurrentLease(n), Clock)

ShouldReplaceLease(lease) ==
    \/ lease.node = NoNode
    \/ Clock > lease.expiration

\* Incorrect optimization: also replace the lease when the leader holds it.
IncorrectShouldReplaceLease(lease) ==
    \/ ShouldReplaceLease(lease)
    \/ lease.node = Leader

-----------------------------------------------------------------------------------

TypeInvariant ==
    /\ IsNodeUp \in [Node -> BOOLEAN]
    /\ Leader \in Node
    /\ ReplicatedLog \in Seq(Entry)
    /\ Len(ReplicatedLog) <= MaxLog
    /\ ExecutionCounter \in [Node -> 0 .. MaxLog]
    /\ \A n \in Node : ExecutionCounter[n] <= Len(ReplicatedLog)
    /\ IsTakingCheckpoint \in [Node -> BOOLEAN]
    /\ LatestCheckpoint \in [Node -> 0 .. MaxLog]
    /\ Clock \in NatBound

SafetyInvariant ==
    \* The leader never takes a checkpoint
    /\ \A n \in Node : IsTakingCheckpoint[n] => n # Leader
    \* At most one node takes a checkpoint at any time
    /\ \A n, m \in Node :
          (IsTakingCheckpoint[n] /\ IsTakingCheckpoint[m]) => n = m
    \* A checkpointing node holds a valid lease
    /\ \A n \in Node : IsTakingCheckpoint[n] => HasLease(n)

-----------------------------------------------------------------------------------

Init ==
    /\ IsNodeUp = [n \in Node |-> TRUE]
    /\ Leader \in Node
    /\ ReplicatedLog = << >>
    /\ ExecutionCounter = [n \in Node |-> 0]
    /\ IsTakingCheckpoint = [n \in Node |-> FALSE]
    /\ LatestCheckpoint = [n \in Node |-> 0]
    /\ Clock = 0

Tick ==
    /\ Clock < MaxNat
    /\ Clock' = Clock + 1
    \* Nodes whose lease expires immediately abandon their checkpoint
    /\ IsTakingCheckpoint' =
         [n \in Node |-> IsTakingCheckpoint[n]
                           /\ LeaseValid(CurrentLease(n), Clock + 1)]
    /\ UNCHANGED << IsNodeUp, Leader, ReplicatedLog, ExecutionCounter,
                    LatestCheckpoint >>

ExecuteEntry(n) ==
    /\ IsNodeUp[n]
    /\ ~IsTakingCheckpoint[n]
    /\ ExecutionCounter[n] < Len(ReplicatedLog)
    /\ ExecutionCounter' = [ExecutionCounter EXCEPT ![n] = @ + 1]
    /\ UNCHANGED << IsNodeUp, Leader, ReplicatedLog, IsTakingCheckpoint,
                    LatestCheckpoint, Clock >>

AppendOp ==
    /\ IsNodeUp[Leader]
    /\ OpenIndices # {}
    /\ ReplicatedLog' = Append(ReplicatedLog,
                          [type |-> "Op", node |-> NoNode, expiration |-> 0])
    /\ UNCHANGED << IsNodeUp, Leader, ExecutionCounter, IsTakingCheckpoint,
                    LatestCheckpoint, Clock >>

AppendLease(m) ==
    /\ IsNodeUp[Leader]
    /\ m # Leader
    /\ OpenIndices # {}
    /\ ExecutionCounter[Leader] = Len(ReplicatedLog)
    /\ ShouldReplaceLease(CurrentLease(Leader))
    /\ ReplicatedLog' = Append(ReplicatedLog,
                          [type |-> "Lease", node |-> m,
                           expiration |-> Min(Clock + LeaseDuration, MaxNat)])
    /\ UNCHANGED << IsNodeUp, Leader, ExecutionCounter, IsTakingCheckpoint,
                    LatestCheckpoint, Clock >>

StartCheckpoint(n) ==
    /\ IsNodeUp[n]
    /\ n # Leader
    /\ ~IsTakingCheckpoint[n]
    /\ HasLease(n)
    /\ IsTakingCheckpoint' = [IsTakingCheckpoint EXCEPT ![n] = TRUE]
    /\ UNCHANGED << IsNodeUp, Leader, ReplicatedLog, ExecutionCounter,
                    LatestCheckpoint, Clock >>

FinishCheckpoint(n) ==
    /\ IsNodeUp[n]
    /\ IsTakingCheckpoint[n]
    /\ HasLease(n)
    /\ IsTakingCheckpoint' = [IsTakingCheckpoint EXCEPT ![n] = FALSE]
    /\ LatestCheckpoint' = [LatestCheckpoint EXCEPT ![n] = ExecutionCounter[n]]
    /\ UNCHANGED << IsNodeUp, Leader, ReplicatedLog, ExecutionCounter, Clock >>

ElectLeader(n) ==
    /\ \E Q \in Quorums :
          /\ n \in Q
          /\ \A q \in Q : IsNodeUp[q]
    /\ Leader' = n
    /\ ExecutionCounter' = [ExecutionCounter EXCEPT ![n] = Len(ReplicatedLog)]
    /\ IsTakingCheckpoint' = [IsTakingCheckpoint EXCEPT ![n] = FALSE]
    /\ UNCHANGED << IsNodeUp, ReplicatedLog, LatestCheckpoint, Clock >>

NodeFailure(n) ==
    /\ IsNodeUp[n]
    /\ IsNodeUp' = [IsNodeUp EXCEPT ![n] = FALSE]
    /\ IsTakingCheckpoint' = [IsTakingCheckpoint EXCEPT ![n] = FALSE]
    /\ UNCHANGED << Leader, ReplicatedLog, ExecutionCounter,
                    LatestCheckpoint, Clock >>

NodeRecovery(n) ==
    /\ ~IsNodeUp[n]
    /\ IsNodeUp' = [IsNodeUp EXCEPT ![n] = TRUE]
    /\ ExecutionCounter' = [ExecutionCounter EXCEPT ![n] = LatestCheckpoint[n]]
    /\ UNCHANGED << Leader, ReplicatedLog, IsTakingCheckpoint,
                    LatestCheckpoint, Clock >>

Next ==
    \/ Tick
    \/ AppendOp
    \/ \E n \in Node :
          \/ ExecuteEntry(n)
          \/ AppendLease(n)
          \/ StartCheckpoint(n)
          \/ FinishCheckpoint(n)
          \/ ElectLeader(n)
          \/ NodeFailure(n)
          \/ NodeRecovery(n)

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------------
\* Model-checking configuration helpers

StateConstraint == OpenIndices # {}

Symmetry == Permutations(Node)

THEOREM Spec => [](TypeInvariant /\ SafetyInvariant)

===================================================================================