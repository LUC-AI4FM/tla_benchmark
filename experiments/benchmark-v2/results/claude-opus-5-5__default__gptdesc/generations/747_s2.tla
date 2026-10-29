------------------------- MODULE CheckpointCoordination -------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
    Nodes,           \* set of replica identifiers
    LeaseDuration,   \* number of ticks a checkpoint lease remains valid
    MaxRequests      \* bound on the number of client requests replicated

ASSUME LeaseDuration \in Nat \ {0}
ASSUME MaxRequests \in Nat
ASSUME Cardinality(Nodes) >= 2

None == CHOOSE x : x \notin Nodes

VARIABLES
    \* ---------------- environment state ----------------
    up,            \* up[n]    : node n is alive
    netUp,         \* netUp[n] : node n is connected to the network
    time,          \* global logical clock used for lease expiry
    \* ---------------- Paxos / RSL state ----------------
    leader,        \* current primary, or None
    ballot,        \* current ballot / view number
    log,           \* log[n]   : replicated log as known by node n
    reqCount,      \* number of client requests replicated so far
    \* ---------------- checkpoint state -----------------
    checkpointing, \* checkpointing[n] : node n is currently taking a checkpoint
    ckptCount      \* number of completed checkpoints

envVars    == <<up, netUp, time>>
paxosVars  == <<leader, ballot, log, reqCount>>
ckptVars   == <<checkpointing, ckptCount>>
vars       == <<up, netUp, time, leader, ballot, log, reqCount,
                checkpointing, ckptCount>>

-----------------------------------------------------------------------------
(* Log entries *)

EntryTypes == {"req", "lease"}

Entry == [type : EntryTypes, node : Nodes, expires : Nat]

NoLease == [type |-> "none", node |-> None, expires |-> 0]

MaxOf(S) == CHOOSE i \in S : \A j \in S : j <= i

LeaseIndices(l) == {i \in 1..Len(l) : l[i].type = "lease"}

LastLease(l) ==
    IF LeaseIndices(l) = {} THEN NoLease ELSE l[MaxOf(LeaseIndices(l))]

IsPrefix(a, b) ==
    /\ Len(a) <= Len(b)
    /\ SubSeq(b, 1, Len(a)) = a

-----------------------------------------------------------------------------
(* Derived predicates *)

Reachable(n) == up[n] /\ netUp[n]

QuorumReachable ==
    2 * Cardinality({m \in Nodes : Reachable(m)}) > Cardinality(Nodes)

HoldsLease(n) ==
    /\ LastLease(log[n]).node = n
    /\ LastLease(log[n]).expires > time

\* An eligible node is a non-primary replica that is up and holds a valid lease
CanStartCheckpoint(n) ==
    /\ up[n]
    /\ n # leader
    /\ ~checkpointing[n]
    /\ HoldsLease(n)

-----------------------------------------------------------------------------
Init ==
    /\ up            = [n \in Nodes |-> TRUE]
    /\ netUp         = [n \in Nodes |-> TRUE]
    /\ time          = 0
    /\ leader        = None
    /\ ballot        = 0
    /\ log           = [n \in Nodes |-> << >>]
    /\ reqCount      = 0
    /\ checkpointing = [n \in Nodes |-> FALSE]
    /\ ckptCount     = 0

-----------------------------------------------------------------------------
(* Environment actions *)

NodeFail(n) ==
    /\ up[n]
    /\ up' = [up EXCEPT ![n] = FALSE]
    /\ leader' = IF leader = n THEN None ELSE leader
    /\ checkpointing' = [checkpointing EXCEPT ![n] = FALSE]
    /\ UNCHANGED <<netUp, time, ballot, log, reqCount, ckptCount>>

NodeRecover(n) ==
    /\ ~up[n]
    /\ up' = [up EXCEPT ![n] = TRUE]
    /\ UNCHANGED <<netUp, time, leader, ballot, log, reqCount,
                   checkpointing, ckptCount>>

NetFail(n) ==
    /\ netUp[n]
    /\ netUp' = [netUp EXCEPT ![n] = FALSE]
    /\ leader' = IF leader = n THEN None ELSE leader
    /\ UNCHANGED <<up, time, ballot, log, reqCount, checkpointing, ckptCount>>

NetRecover(n) ==
    /\ ~netUp[n]
    /\ netUp' = [netUp EXCEPT ![n] = TRUE]
    /\ UNCHANGED <<up, time, leader, ballot, log, reqCount,
                   checkpointing, ckptCount>>

\* Time advances; checkpoints whose lease expires are aborted
Tick ==
    /\ time' = time + 1
    /\ checkpointing' =
         [n \in Nodes |->
            /\ checkpointing[n]
            /\ LastLease(log[n]).node = n
            /\ LastLease(log[n]).expires > time + 1]
    /\ UNCHANGED <<up, netUp, leader, ballot, log, reqCount, ckptCount>>

-----------------------------------------------------------------------------
(* Paxos / RSL actions *)

ElectLeader(n) ==
    /\ leader = None
    /\ Reachable(n)
    /\ QuorumReachable
    /\ \A m \in Nodes : Len(log[m]) <= Len(log[n])
    /\ leader' = n
    /\ ballot' = ballot + 1
    /\ checkpointing' = [checkpointing EXCEPT ![n] = FALSE]
    /\ UNCHANGED <<up, netUp, time, log, reqCount, ckptCount>>

ClientRequest ==
    /\ leader # None
    /\ reqCount < MaxRequests
    /\ log' = [log EXCEPT ![leader] =
                 Append(log[leader],
                        [type |-> "req", node |-> leader, expires |-> 0])]
    /\ reqCount' = reqCount + 1
    /\ UNCHANGED <<up, netUp, time, leader, ballot, checkpointing, ckptCount>>

Replicate(m) ==
    /\ leader # None
    /\ m # leader
    /\ Reachable(m)
    /\ log[m] # log[leader]
    /\ log' = [log EXCEPT ![m] = log[leader]]
    /\ UNCHANGED <<up, netUp, time, leader, ballot, reqCount,
                   checkpointing, ckptCount>>

\* The primary grants a checkpoint lease through the replicated log, only once
\* the previous lease has expired
GrantLease(c) ==
    /\ leader # None
    /\ c # leader
    /\ up[c]
    /\ LastLease(log[leader]).expires <= time
    /\ log' = [log EXCEPT ![leader] =
                 Append(log[leader],
                        [type |-> "lease", node |-> c,
                         expires |-> time + LeaseDuration])]
    /\ UNCHANGED <<up, netUp, time, leader, ballot, reqCount,
                   checkpointing, ckptCount>>

-----------------------------------------------------------------------------
(* Checkpoint actions *)

StartCheckpoint(n) ==
    /\ CanStartCheckpoint(n)
    /\ checkpointing' = [checkpointing EXCEPT ![n] = TRUE]
    /\ UNCHANGED <<up, netUp, time, leader, ballot, log, reqCount, ckptCount>>

CompleteCheckpoint(n) ==
    /\ checkpointing[n]
    /\ up[n]
    /\ HoldsLease(n)
    /\ checkpointing' = [checkpointing EXCEPT ![n] = FALSE]
    /\ ckptCount' = ckptCount + 1
    /\ UNCHANGED <<up, netUp, time, leader, ballot, log, reqCount>>

-----------------------------------------------------------------------------
EnvNext ==
    \/ \E n \in Nodes : NodeFail(n) \/ NodeRecover(n)
                        \/ NetFail(n) \/ NetRecover(n)
    \/ Tick

PaxosNext ==
    \/ \E n \in Nodes : ElectLeader(n) \/ Replicate(n) \/ GrantLease(n)
    \/ ClientRequest

CkptNext ==
    \E n \in Nodes : StartCheckpoint(n) \/ CompleteCheckpoint(n)

Next == EnvNext \/ PaxosNext \/ CkptNext

Fairness ==
    /\ WF_vars(Tick)
    /\ \A n \in Nodes : WF_vars(ElectLeader(n))
    /\ \A n \in Nodes : WF_vars(Replicate(n))
    /\ \A n \in Nodes : WF_vars(GrantLease(n))
    /\ \A n \in Nodes : WF_vars(StartCheckpoint(n))
    /\ \A n \in Nodes : SF_vars(CompleteCheckpoint(n))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Invariants *)

TypeOK ==
    /\ up \in [Nodes -> BOOLEAN]
    /\ netUp \in [Nodes -> BOOLEAN]
    /\ time \in Nat
    /\ leader \in Nodes \cup {None}
    /\ ballot \in Nat
    /\ log \in [Nodes -> Seq(Entry)]
    /\ reqCount \in 0..MaxRequests
    /\ checkpointing \in [Nodes -> BOOLEAN]
    /\ ckptCount \in Nat

\* Logs never conflict: any two logs are prefix-related
LogsConsistent ==
    \A n, m \in Nodes : IsPrefix(log[n], log[m]) \/ IsPrefix(log[m], log[n])

\* At most one node holds a valid checkpoint lease
UniqueLeaseOwner ==
    \A n, m \in Nodes : (HoldsLease(n) /\ HoldsLease(m)) => n = m

\* A checkpointing node holds the lease, is up and is not the primary;
\* at most one node checkpoints at a time
CheckpointSafety ==
    /\ \A n \in Nodes : checkpointing[n] => (up[n] /\ HoldsLease(n) /\ n # leader)
    /\ \A n, m \in Nodes : (checkpointing[n] /\ checkpointing[m]) => n = m

LeaderSane ==
    leader # None => Reachable(leader)

Safety ==
    /\ LogsConsistent
    /\ UniqueLeaseOwner
    /\ CheckpointSafety
    /\ LeaderSane

-----------------------------------------------------------------------------
(* Liveness properties *)

EventuallyStable == <>[](\A n \in Nodes : up[n] /\ netUp[n])

\* Under a stable environment, checkpoint opportunities keep arising
CheckpointOpportunity ==
    EventuallyStable => []<>(\E n \in Nodes : CanStartCheckpoint(n))

\* Under a stable environment, some checkpoint eventually completes
CheckpointEventuallyCompletes ==
    EventuallyStable => <>(ckptCount > 0)

\* Any checkpoint in progress eventually finishes (completes or is aborted)
CheckpointTerminates ==
    \A n \in Nodes : checkpointing[n] ~> ~checkpointing[n]

Liveness ==
    /\ CheckpointOpportunity
    /\ CheckpointEventuallyCompletes
    /\ CheckpointTerminates

THEOREM Spec => [](TypeOK /\ Safety)
THEOREM Spec => Liveness
=============================================================================