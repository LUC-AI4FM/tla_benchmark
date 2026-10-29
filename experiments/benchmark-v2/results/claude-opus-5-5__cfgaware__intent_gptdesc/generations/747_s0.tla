---------------------------- MODULE CheckpointCoordination ----------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
    Node,       \* The set of nodes in the cluster
    LogIndex,   \* The set of log indices (assumed to be 1..k)
    NoNode      \* Placeholder value meaning "no node"

ASSUME NoNode \notin Node
ASSUME LogIndex \subseteq (Nat \ {0}) /\ LogIndex /= {}

VARIABLES
    IsNodeUp,            \* Whether each node is up
    NetworkPath,         \* Whether each directed network link is up
    ReplicatedLog,       \* Each node's copy of the replicated log
    ExecutionCounter,    \* Number of log entries each node has executed
    Leader,              \* Current leader, or NoNode
    CheckpointLease,     \* The current checkpoint lease
    LeaseExpired,        \* Whether the current lease has timed out
    CanTakeCheckpoint,   \* Whether each node is eligible to checkpoint
    IsTakingCheckpoint,  \* Whether each node is taking a checkpoint
    LatestCheckpoint     \* The latest persisted snapshot

vars == <<IsNodeUp, NetworkPath, ReplicatedLog, ExecutionCounter, Leader,
          CheckpointLease, LeaseExpired, CanTakeCheckpoint,
          IsTakingCheckpoint, LatestCheckpoint>>

-----------------------------------------------------------------------------------------
(* Helper definitions *)

MaxIndex == CHOOSE i \in LogIndex : \A j \in LogIndex : j <= i

\* Log entries: a node ID means "this node should checkpoint at this index";
\* NoNode means an ordinary (blank) command.
LogEntry == Node \cup {NoNode}

BoundedSeq(S) == UNION {[1..k -> S] : k \in 0..MaxIndex}

NoCheckpointLease == [node |-> NoNode, counter |-> 0]

BlankCheckpoint == [log |-> << >>, counter |-> 0]

\* Log indices not yet filled on any node
OpenIndices ==
    {i \in LogIndex : \A n \in Node : i > Len(ReplicatedLog[n])}

\* The lowest open index of a node's log
OpenIndex(n) == Len(ReplicatedLog[n]) + 1

\* Whether a lease may be replaced by a new one
ShouldReplaceLease(lease) ==
    \/ lease = NoCheckpointLease
    \/ LeaseExpired

Connected(a, b) ==
    /\ NetworkPath[<<a, b>>]
    /\ NetworkPath[<<b, a>>]

Reachable(n) ==
    {m \in Node : IsNodeUp[m] /\ (m = n \/ Connected(n, m))}

HasQuorum(n) == 2 * Cardinality(Reachable(n)) > Cardinality(Node)

IsPrefix(s, t) ==
    /\ Len(s) <= Len(t)
    /\ SubSeq(t, 1, Len(s)) = s

-----------------------------------------------------------------------------------------
(* Type invariant *)

TypeInvariant ==
    /\ IsNodeUp \in [Node -> BOOLEAN]
    /\ NetworkPath \in [Node \X Node -> BOOLEAN]
    /\ ReplicatedLog \in [Node -> BoundedSeq(LogEntry)]
    /\ ExecutionCounter \in [Node -> 0..MaxIndex]
    /\ \A n \in Node : ExecutionCounter[n] <= Len(ReplicatedLog[n])
    /\ Leader \in Node \cup {NoNode}
    /\ CheckpointLease \in [node : Node \cup {NoNode}, counter : 0..MaxIndex]
    /\ LeaseExpired \in BOOLEAN
    /\ CanTakeCheckpoint \in [Node -> BOOLEAN]
    /\ IsTakingCheckpoint \in [Node -> BOOLEAN]
    /\ LatestCheckpoint \in [log : BoundedSeq(LogEntry), counter : 0..MaxIndex]

-----------------------------------------------------------------------------------------
(* Initial state *)

Init ==
    /\ IsNodeUp = [n \in Node |-> TRUE]
    /\ NetworkPath = [p \in Node \X Node |-> TRUE]
    /\ ReplicatedLog = [n \in Node |-> << >>]
    /\ ExecutionCounter = [n \in Node |-> 0]
    /\ Leader = NoNode
    /\ CheckpointLease = NoCheckpointLease
    /\ LeaseExpired = FALSE
    /\ CanTakeCheckpoint = [n \in Node |-> FALSE]
    /\ IsTakingCheckpoint = [n \in Node |-> FALSE]
    /\ LatestCheckpoint = BlankCheckpoint

-----------------------------------------------------------------------------------------
(* Failures and recoveries *)

NodeFail(n) ==
    /\ IsNodeUp[n]
    /\ IsNodeUp' = [IsNodeUp EXCEPT ![n] = FALSE]
    /\ CanTakeCheckpoint' = [CanTakeCheckpoint EXCEPT ![n] = FALSE]
    /\ IsTakingCheckpoint' = [IsTakingCheckpoint EXCEPT ![n] = FALSE]
    /\ Leader' = IF Leader = n THEN NoNode ELSE Leader
    /\ UNCHANGED <<NetworkPath, ReplicatedLog, ExecutionCounter,
                   CheckpointLease, LeaseExpired, LatestCheckpoint>>

NodeRecover(n) ==
    /\ ~IsNodeUp[n]
    /\ IsNodeUp' = [IsNodeUp EXCEPT ![n] = TRUE]
    /\ UNCHANGED <<NetworkPath, ReplicatedLog, ExecutionCounter, Leader,
                   CheckpointLease, LeaseExpired, CanTakeCheckpoint,
                   IsTakingCheckpoint, LatestCheckpoint>>

LinkFail(a, b) ==
    /\ a /= b
    /\ NetworkPath[<<a, b>>]
    /\ NetworkPath' = [NetworkPath EXCEPT ![<<a, b>>] = FALSE]
    /\ UNCHANGED <<IsNodeUp, ReplicatedLog, ExecutionCounter, Leader,
                   CheckpointLease, LeaseExpired, CanTakeCheckpoint,
                   IsTakingCheckpoint, LatestCheckpoint>>

LinkRecover(a, b) ==
    /\ a /= b
    /\ ~NetworkPath[<<a, b>>]
    /\ NetworkPath' = [NetworkPath EXCEPT ![<<a, b>>] = TRUE]
    /\ UNCHANGED <<IsNodeUp, ReplicatedLog, ExecutionCounter, Leader,
                   CheckpointLease, LeaseExpired, CanTakeCheckpoint,
                   IsTakingCheckpoint, LatestCheckpoint>>

-----------------------------------------------------------------------------------------
(* Leadership *)

\* A node can become leader only with quorum and when fully caught up
ElectLeader(n) ==
    /\ Leader = NoNode
    /\ IsNodeUp[n]
    /\ HasQuorum(n)
    /\ ExecutionCounter[n] = Len(ReplicatedLog[n])
    /\ \A m \in Node : Len(ReplicatedLog[m]) <= Len(ReplicatedLog[n])
    /\ ~CanTakeCheckpoint[n]
    /\ ~IsTakingCheckpoint[n]
    /\ Leader' = n
    /\ UNCHANGED <<IsNodeUp, NetworkPath, ReplicatedLog, ExecutionCounter,
                   CheckpointLease, LeaseExpired, CanTakeCheckpoint,
                   IsTakingCheckpoint, LatestCheckpoint>>

LeaderDeposed ==
    /\ Leader /= NoNode
    /\ ~HasQuorum(Leader)
    /\ Leader' = NoNode
    /\ UNCHANGED <<IsNodeUp, NetworkPath, ReplicatedLog, ExecutionCounter,
                   CheckpointLease, LeaseExpired, CanTakeCheckpoint,
                   IsTakingCheckpoint, LatestCheckpoint>>

-----------------------------------------------------------------------------------------
(* Log replication and execution *)

\* Leader appends an ordinary (blank) command
LeaderAppendBlank ==
    /\ Leader /= NoNode
    /\ IsNodeUp[Leader]
    /\ OpenIndex(Leader) \in LogIndex
    /\ ReplicatedLog' = [ReplicatedLog EXCEPT ![Leader] = Append(@, NoNode)]
    /\ UNCHANGED <<IsNodeUp, NetworkPath, ExecutionCounter, Leader,
                   CheckpointLease, LeaseExpired, CanTakeCheckpoint,
                   IsTakingCheckpoint, LatestCheckpoint>>

\* Leader proposes that replica n checkpoint at the current open log index
LeaderProposeCheckpoint(n) ==
    /\ Leader /= NoNode
    /\ IsNodeUp[Leader]
    /\ n \in Node \ {Leader}
    /\ ShouldReplaceLease(CheckpointLease)
    /\ \A m \in Node : ~CanTakeCheckpoint[m] /\ ~IsTakingCheckpoint[m]
    /\ OpenIndex(Leader) \in LogIndex
    /\ ReplicatedLog' = [ReplicatedLog EXCEPT ![Leader] = Append(@, n)]
    /\ CheckpointLease' = [node |-> n, counter |-> OpenIndex(Leader)]
    /\ LeaseExpired' = FALSE
    /\ UNCHANGED <<IsNodeUp, NetworkPath, ExecutionCounter, Leader,
                   CanTakeCheckpoint, IsTakingCheckpoint, LatestCheckpoint>>

\* A node with a longer log disseminates the next entry to a reachable node
ReplicateEntry(src, dst) ==
    /\ src /= dst
    /\ IsNodeUp[src]
    /\ IsNodeUp[dst]
    /\ NetworkPath[<<src, dst>>]
    /\ Len(ReplicatedLog[dst]) < Len(ReplicatedLog[src])
    /\ ReplicatedLog' = [ReplicatedLog EXCEPT ![dst] =
            Append(@, ReplicatedLog[src][Len(ReplicatedLog[dst]) + 1])]
    /\ UNCHANGED <<IsNodeUp, NetworkPath, ExecutionCounter, Leader,
                   CheckpointLease, LeaseExpired, CanTakeCheckpoint,
                   IsTakingCheckpoint, LatestCheckpoint>>

\* A node executes its next log entry (paused while checkpointing)
ExecuteEntry(n) ==
    /\ IsNodeUp[n]
    /\ ~IsTakingCheckpoint[n]
    /\ ExecutionCounter[n] < Len(ReplicatedLog[n])
    /\ ExecutionCounter' = [ExecutionCounter EXCEPT ![n] = @ + 1]
    /\ UNCHANGED <<IsNodeUp, NetworkPath, ReplicatedLog, Leader,
                   CheckpointLease, LeaseExpired, CanTakeCheckpoint,
                   IsTakingCheckpoint, LatestCheckpoint>>

-----------------------------------------------------------------------------------------
(* Checkpoint lease and checkpointing *)

\* The lease times out; the holder detects this and abandons checkpointing
LeaseTimeout ==
    /\ CheckpointLease /= NoCheckpointLease
    /\ ~LeaseExpired
    /\ LeaseExpired' = TRUE
    /\ CanTakeCheckpoint' = [CanTakeCheckpoint EXCEPT ![CheckpointLease.node] = FALSE]
    /\ IsTakingCheckpoint' = [IsTakingCheckpoint EXCEPT ![CheckpointLease.node] = FALSE]
    /\ UNCHANGED <<IsNodeUp, NetworkPath, ReplicatedLog, ExecutionCounter,
                   Leader, CheckpointLease, LatestCheckpoint>>

\* A node marks itself eligible to checkpoint
MarkCanTakeCheckpoint(n) ==
    /\ IsNodeUp[n]
    /\ n /= Leader
    /\ CheckpointLease.node = n
    /\ ~LeaseExpired
    /\ ExecutionCounter[n] >= CheckpointLease.counter
    /\ ReplicatedLog[n][CheckpointLease.counter] = n
    /\ \A m \in Node : ~CanTakeCheckpoint[m] /\ ~IsTakingCheckpoint[m]
    /\ CanTakeCheckpoint' = [CanTakeCheckpoint EXCEPT ![n] = TRUE]
    /\ UNCHANGED <<IsNodeUp, NetworkPath, ReplicatedLog, ExecutionCounter,
                   Leader, CheckpointLease, LeaseExpired,
                   IsTakingCheckpoint, LatestCheckpoint>>

\* An eligible node begins checkpointing (mutually exclusive)
StartCheckpoint(n) ==
    /\ IsNodeUp[n]
    /\ CanTakeCheckpoint[n]
    /\ \A m \in Node : ~IsTakingCheckpoint[m]
    /\ IsTakingCheckpoint' = [IsTakingCheckpoint EXCEPT ![n] = TRUE]
    /\ CanTakeCheckpoint' = [CanTakeCheckpoint EXCEPT ![n] = FALSE]
    /\ UNCHANGED <<IsNodeUp, NetworkPath, ReplicatedLog, ExecutionCounter,
                   Leader, CheckpointLease, LeaseExpired, LatestCheckpoint>>

\* The checkpointing node reports progress, renewing its lease
ReportProgress(n) ==
    /\ IsNodeUp[n]
    /\ IsTakingCheckpoint[n]
    /\ Leader /= NoNode
    /\ IsNodeUp[Leader]
    /\ Connected(n, Leader)
    /\ CheckpointLease.node = n
    /\ CheckpointLease' = [node |-> n, counter |-> ExecutionCounter[n]]
    /\ LeaseExpired' = FALSE
    /\ CheckpointLease' /= CheckpointLease
    /\ UNCHANGED <<IsNodeUp, NetworkPath, ReplicatedLog, ExecutionCounter,
                   Leader, CanTakeCheckpoint, IsTakingCheckpoint,
                   LatestCheckpoint>>

\* The checkpointing node persists a snapshot and clears the lease
FinishCheckpoint(n) ==
    /\ IsNodeUp[n]
    /\ IsTakingCheckpoint[n]
    /\ LatestCheckpoint' =
            IF ExecutionCounter[n] >= LatestCheckpoint.counter
            THEN [log |-> SubSeq(ReplicatedLog[n], 1, ExecutionCounter[n]),
                  counter |-> ExecutionCounter[n]]
            ELSE LatestCheckpoint
    /\ IsTakingCheckpoint' = [IsTakingCheckpoint EXCEPT ![n] = FALSE]
    /\ CheckpointLease' = NoCheckpointLease
    /\ LeaseExpired' = FALSE
    /\ UNCHANGED <<IsNodeUp, NetworkPath, ReplicatedLog, ExecutionCounter,
                   Leader, CanTakeCheckpoint>>

-----------------------------------------------------------------------------------------
(* Specification *)

Next ==
    \/ \E n \in Node : NodeFail(n)
    \/ \E n \in Node : NodeRecover(n)
    \/ \E a, b \in Node : LinkFail(a, b)
    \/ \E a, b \in Node : LinkRecover(a, b)
    \/ \E n \in Node : ElectLeader(n)
    \/ LeaderDeposed
    \/ LeaderAppendBlank
    \/ \E n \in Node : LeaderProposeCheckpoint(n)
    \/ \E a, b \in Node : ReplicateEntry(a, b)
    \/ \E n \in Node : ExecuteEntry(n)
    \/ LeaseTimeout
    \/ \E n \in Node : MarkCanTakeCheckpoint(n)
    \/ \E n \in Node : StartCheckpoint(n)
    \/ \E n \in Node : ReportProgress(n)
    \/ \E n \in Node : FinishCheckpoint(n)

Fairness ==
    /\ \A n \in Node : WF_vars(ElectLeader(n))
    /\ \A n \in Node : WF_vars(LeaderProposeCheckpoint(n))
    /\ \A a, b \in Node : WF_vars(ReplicateEntry(a, b))
    /\ \A n \in Node : WF_vars(ExecuteEntry(n))
    /\ \A n \in Node : WF_vars(MarkCanTakeCheckpoint(n))
    /\ \A n \in Node : WF_vars(StartCheckpoint(n))
    /\ \A n \in Node : WF_vars(FinishCheckpoint(n))
    /\ WF_vars(LeaseTimeout)

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------------------
(* Safety properties *)

\* At most one node is eligible or actively checkpointing
CheckpointExclusivity ==
    \A m, n \in Node :
        ((CanTakeCheckpoint[m] \/ IsTakingCheckpoint[m]) /\
         (CanTakeCheckpoint[n] \/ IsTakingCheckpoint[n])) => m = n

\* The leader never takes a checkpoint
LeaderNeverCheckpoints ==
    Leader /= NoNode =>
        (~CanTakeCheckpoint[Leader] /\ ~IsTakingCheckpoint[Leader])

\* Eligibility/checkpointing implies holding the lease
LeaseImpliesExclusivity ==
    \A n \in Node :
        (CanTakeCheckpoint[n] \/ IsTakingCheckpoint[n]) =>
            CheckpointLease.node = n

\* Replicated logs never contain conflicting entries
LogsConsistent ==
    \A m, n \in Node :
        IsPrefix(ReplicatedLog[m], ReplicatedLog[n]) \/
        IsPrefix(ReplicatedLog[n], ReplicatedLog[m])

SafetyInvariant ==
    /\ CheckpointExclusivity
    /\ LeaderNeverCheckpoints
    /\ LeaseImpliesExclusivity
    /\ LogsConsistent

-----------------------------------------------------------------------------------------
(* Liveness properties *)

EventuallyEligible == <>(\E n \in Node : CanTakeCheckpoint[n])

EligibleEventuallyStarts ==
    \A n \in Node :
        CanTakeCheckpoint[n] ~>
            (IsTakingCheckpoint[n] \/ ~IsNodeUp[n] \/ LeaseExpired)

CheckpointEventuallyEnds ==
    \A n \in Node :
        IsTakingCheckpoint[n] ~>
            (~IsTakingCheckpoint[n] \/ ~IsNodeUp[n] \/ LeaseExpired)

EventuallyCheckpoint == <>(LatestCheckpoint.counter > 0)

=========================================================================================