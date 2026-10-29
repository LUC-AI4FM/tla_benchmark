------------------------- MODULE PaxosCheckpointLease -------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
    Nodes,          \* set of replica identifiers
    None,           \* placeholder value meaning "no node"
    LeaseDuration,  \* length of a checkpoint lease (in clock ticks)
    MaxTime,        \* bound on the global clock (for finite model checking)
    MaxLogLen,      \* bound on replicated log length
    MaxFailures     \* bound on the number of injected failures

ASSUME
    /\ Nodes # {}
    /\ None \notin Nodes
    /\ LeaseDuration \in Nat \ {0}
    /\ MaxTime \in Nat
    /\ MaxLogLen \in Nat
    /\ MaxFailures \in Nat

-----------------------------------------------------------------------------
(* Environment state *)
VARIABLES
    up,          \* set of nodes that are currently running
    connected,   \* set of nodes currently connected to the network
    failures,    \* number of failures injected so far
    time         \* global logical clock used for lease expiry

(* Paxos-related state *)
VARIABLES
    leader,      \* current primary, or None
    ballot,      \* current ballot / view number
    log          \* log[n] : replicated log as held by node n

(* Checkpoint-specific state *)
VARIABLES
    checkpointing, \* set of nodes currently taking a checkpoint
    ckptCount      \* number of checkpoints successfully completed

envVars   == <<up, connected, failures, time>>
paxosVars == <<leader, ballot, log>>
ckptVars  == <<checkpointing, ckptCount>>
vars      == <<envVars, paxosVars, ckptVars>>

-----------------------------------------------------------------------------
(* Helper definitions *)

Quorums == {Q \in SUBSET Nodes : 2 * Cardinality(Q) > Cardinality(Nodes)}

Alive == up \cap connected

MaxOf(S) == CHOOSE x \in S : \A y \in S : x >= y

RequestEntries == [type : {"request"}, node : Nodes, exp : {0}]
LeaseEntries   == [type : {"lease"}, node : Nodes,
                   exp : 0..(MaxTime + LeaseDuration)]
Entries == RequestEntries \cup LeaseEntries

IsPrefix(s, t) ==
    /\ Len(s) <= Len(t)
    /\ \A i \in 1..Len(s) : s[i] = t[i]

LeaseIdx(l) == {i \in 1..Len(l) : l[i].type = "lease"}

HasLease(l) == LeaseIdx(l) # {}

LastLease(l) == l[MaxOf(LeaseIdx(l))]

LatestExpiry(l) == IF HasLease(l) THEN LastLease(l).exp ELSE 0

\* Node n holds an unexpired checkpoint lease according to its own log
HoldsLease(n) ==
    /\ HasLease(log[n])
    /\ LastLease(log[n]).node = n
    /\ time < LastLease(log[n]).exp

\* Node n is eligible and authorized to start a checkpoint
CanCheckpoint(n) ==
    /\ n \in Alive
    /\ n # leader
    /\ HoldsLease(n)
    /\ n \notin checkpointing

-----------------------------------------------------------------------------
(* Type invariant *)

TypeOK ==
    /\ up \subseteq Nodes
    /\ connected \subseteq Nodes
    /\ failures \in 0..MaxFailures
    /\ time \in 0..MaxTime
    /\ leader \in Nodes \cup {None}
    /\ ballot \in Nat
    /\ log \in [Nodes -> Seq(Entries)]
    /\ \A n \in Nodes : Len(log[n]) <= MaxLogLen
    /\ checkpointing \subseteq Nodes
    /\ ckptCount \in Nat

-----------------------------------------------------------------------------
(* Initial state *)

Init ==
    /\ up = Nodes
    /\ connected = Nodes
    /\ failures = 0
    /\ time = 0
    /\ leader = None
    /\ ballot = 0
    /\ log = [n \in Nodes |-> <<>>]
    /\ checkpointing = {}
    /\ ckptCount = 0

-----------------------------------------------------------------------------
(* Environment actions: node and network failures, clock *)

FailNode(n) ==
    /\ n \in up
    /\ failures < MaxFailures
    /\ up' = up \ {n}
    /\ failures' = failures + 1
    /\ leader' = IF leader = n THEN None ELSE leader
    /\ checkpointing' = checkpointing \ {n}
    /\ UNCHANGED <<connected, time, ballot, log, ckptCount>>

RecoverNode(n) ==
    /\ n \notin up
    /\ up' = up \cup {n}
    /\ UNCHANGED <<connected, failures, time, paxosVars, ckptVars>>

Disconnect(n) ==
    /\ n \in connected
    /\ failures < MaxFailures
    /\ connected' = connected \ {n}
    /\ failures' = failures + 1
    /\ UNCHANGED <<up, time, paxosVars, ckptVars>>

Reconnect(n) ==
    /\ n \notin connected
    /\ connected' = connected \cup {n}
    /\ UNCHANGED <<up, failures, time, paxosVars, ckptVars>>

\* Time advances; checkpoints whose lease would expire are aborted.
Tick ==
    /\ time < MaxTime
    /\ time' = time + 1
    /\ checkpointing' =
         {n \in checkpointing :
            /\ HasLease(log[n])
            /\ LastLease(log[n]).node = n
            /\ LastLease(log[n]).exp > time + 1}
    /\ UNCHANGED <<up, connected, failures, paxosVars, ckptCount>>

-----------------------------------------------------------------------------
(* Paxos actions: leader election and replication *)

\* A live node becomes leader if supported by a live quorum whose logs
\* are no longer than its own (so it holds every chosen entry).
ElectLeader(n) ==
    /\ n \in Alive
    /\ \/ leader = None
       \/ leader \notin Alive
    /\ \E Q \in Quorums :
          /\ n \in Q
          /\ Q \subseteq Alive
          /\ \A m \in Q : Len(log[m]) <= Len(log[n])
    /\ leader' = n
    /\ ballot' = ballot + 1
    /\ checkpointing' = checkpointing \ {n}   \* the primary never checkpoints
    /\ UNCHANGED <<envVars, log, ckptCount>>

\* The leader replicates entry e to a live, up-to-date quorum.
Replicate(e) ==
    /\ leader \in Nodes
    /\ leader \in Alive
    /\ Len(log[leader]) < MaxLogLen
    /\ \E Q \in Quorums :
          /\ leader \in Q
          /\ Q \subseteq Alive
          /\ \A m \in Q : log[m] = log[leader]
          /\ log' = [m \in Nodes |->
                       IF m \in Q THEN Append(log[m], e) ELSE log[m]]

\* Client request replicated through Paxos
ReplicateRequest(n) ==
    /\ Replicate([type |-> "request", node |-> n, exp |-> 0])
    /\ UNCHANGED <<envVars, leader, ballot, ckptVars>>

\* A lagging live replica catches up from the leader
CatchUp(n) ==
    /\ leader \in Nodes
    /\ leader \in Alive
    /\ n \in Alive
    /\ n # leader
    /\ Len(log[n]) < Len(log[leader])
    /\ log' = [log EXCEPT ![n] = log[leader]]
    /\ UNCHANGED <<envVars, leader, ballot, ckptVars>>

-----------------------------------------------------------------------------
(* Checkpoint actions *)

\* The leader grants a checkpoint lease to a secondary through the
\* replicated log, only after any previous lease has expired.
GrantLease(n) ==
    /\ leader \in Nodes
    /\ n \in Alive
    /\ n # leader
    /\ time >= LatestExpiry(log[leader])
    /\ Replicate([type |-> "lease", node |-> n,
                  exp |-> time + LeaseDuration])
    /\ UNCHANGED <<envVars, leader, ballot, ckptVars>>

StartCheckpoint(n) ==
    /\ CanCheckpoint(n)
    /\ checkpointing' = checkpointing \cup {n}
    /\ UNCHANGED <<envVars, paxosVars, ckptCount>>

CompleteCheckpoint(n) ==
    /\ n \in checkpointing
    /\ n \in up
    /\ HoldsLease(n)
    /\ checkpointing' = checkpointing \ {n}
    /\ ckptCount' = ckptCount + 1
    /\ UNCHANGED <<envVars, paxosVars>>

-----------------------------------------------------------------------------
(* Next-state relation and specification *)

Next ==
    \/ Tick
    \/ \E n \in Nodes :
          \/ FailNode(n)
          \/ RecoverNode(n)
          \/ Disconnect(n)
          \/ Reconnect(n)
          \/ ElectLeader(n)
          \/ ReplicateRequest(n)
          \/ CatchUp(n)
          \/ GrantLease(n)
          \/ StartCheckpoint(n)
          \/ CompleteCheckpoint(n)

Fairness ==
    /\ WF_vars(\E n \in Nodes : RecoverNode(n))
    /\ WF_vars(\E n \in Nodes : Reconnect(n))
    /\ WF_vars(\E n \in Nodes : ElectLeader(n))
    /\ WF_vars(\E n \in Nodes : CatchUp(n))
    /\ WF_vars(\E n \in Nodes : GrantLease(n))
    /\ WF_vars(\E n \in Nodes : StartCheckpoint(n))
    /\ SF_vars(\E n \in Nodes : CompleteCheckpoint(n))
    /\ WF_vars(Tick)

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Safety *)

\* Logs of any two replicas never conflict: one is a prefix of the other.
LogConsistency ==
    \A m, n \in Nodes : IsPrefix(log[m], log[n]) \/ IsPrefix(log[n], log[m])

\* Every checkpointing node owns a valid, unexpired lease.
LeaseOwnership ==
    \A n \in checkpointing : HoldsLease(n)

\* At most one node checkpoints at a time.
MutualExclusion ==
    \A m, n \in checkpointing : m = n

\* The leader never checkpoints.
LeaderNotCheckpointing ==
    leader \in Nodes => leader \notin checkpointing

Safety ==
    /\ LogConsistency
    /\ LeaseOwnership
    /\ MutualExclusion
    /\ LeaderNotCheckpointing

-----------------------------------------------------------------------------
(* Liveness *)

\* Eventually some node gets an opportunity to checkpoint.
CheckpointOpportunity ==
    <>(\E n \in Nodes : CanCheckpoint(n) \/ n \in checkpointing)

\* Eventually a checkpoint completes.
CheckpointCompletion ==
    <>(ckptCount > 0)

Liveness == CheckpointOpportunity /\ CheckpointCompletion

-----------------------------------------------------------------------------
THEOREM Spec => [](TypeOK /\ Safety)
THEOREM Spec => Liveness
=============================================================================