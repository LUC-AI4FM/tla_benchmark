------------------------------ MODULE PaxosCheckpointLease ------------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
    Node,           \* set of replica nodes
    NoNode,         \* placeholder meaning "no node"
    MaxTime,        \* bound on the logical clock
    LeaseDuration,  \* length of a checkpoint lease
    MaxLogLen,      \* bound on replicated log length
    MaxFailures     \* bound on the number of injected failures

ASSUME /\ NoNode \notin Node
       /\ Node # {}
       /\ MaxTime \in Nat
       /\ LeaseDuration \in Nat \ {0}
       /\ MaxLogLen \in Nat \ {0}
       /\ MaxFailures \in Nat

-----------------------------------------------------------------------------------------
\* Environment state
VARIABLES
    alive,          \* alive[n]: node n is up
    connected,      \* connected[n]: node n is reachable on the network
    clock,          \* global logical time
    failures        \* number of failures injected so far

\* Paxos-related state
VARIABLES
    leader,         \* current primary, or NoNode
    logs,           \* logs[n]: replicated log held by node n
    chosen,         \* the globally committed (chosen) log prefix
    commitIdx       \* commitIdx[n]: committed prefix length known to node n

\* Checkpoint-specific state
VARIABLES
    checkpointing,  \* checkpointing[n]: node n is currently taking a checkpoint
    lastCkpt,       \* lastCkpt[n]: log index covered by n's last checkpoint
    ckptDone        \* set of nodes that have completed at least one checkpoint

envVars   == <<alive, connected, clock, failures>>
paxosVars == <<leader, logs, chosen, commitIdx>>
ckptVars  == <<checkpointing, lastCkpt, ckptDone>>
vars      == <<envVars, paxosVars, ckptVars>>

-----------------------------------------------------------------------------------------
Max(a, b) == IF a >= b THEN a ELSE b
Min(a, b) == IF a <= b THEN a ELSE b

MaxExp == MaxTime + LeaseDuration

Entry == [type : {"req", "lease"}, owner : Node \cup {NoNode}, exp : 0..MaxExp]

ReqEntry == [type |-> "req", owner |-> NoNode, exp |-> 0]
NoLease  == [type |-> "lease", owner |-> NoNode, exp |-> 0]

IsMajority(S) == 2 * Cardinality(S) > Cardinality(Node)

\* The most recent lease entry in a log (or NoLease if none)
LatestLease(s) ==
    IF \E i \in 1..Len(s) : s[i].type = "lease"
    THEN s[CHOOSE i \in 1..Len(s) :
                /\ s[i].type = "lease"
                /\ \A j \in (i+1)..Len(s) : s[j].type # "lease"]
    ELSE NoLease

\* Log s extends (has as prefix) log p
Extends(s, p) == Len(s) >= Len(p) /\ SubSeq(s, 1, Len(p)) = p

\* Committed portion of the log as known by node n
KnownCommitted(n) == SubSeq(logs[n], 1, commitIdx[n])

\* Node n is authorized to checkpoint according to its committed view
HoldsLease(n) ==
    LET L == LatestLease(KnownCommitted(n))
    IN  L.owner = n /\ clock < L.exp

Reachable(n) == alive[n] /\ connected[n]

-----------------------------------------------------------------------------------------
Init ==
    /\ alive         = [n \in Node |-> TRUE]
    /\ connected     = [n \in Node |-> TRUE]
    /\ clock         = 0
    /\ failures      = 0
    /\ leader        = NoNode
    /\ logs          = [n \in Node |-> << >>]
    /\ chosen        = << >>
    /\ commitIdx     = [n \in Node |-> 0]
    /\ checkpointing = [n \in Node |-> FALSE]
    /\ lastCkpt      = [n \in Node |-> 0]
    /\ ckptDone      = {}

-----------------------------------------------------------------------------------------
\* ---------------- Environment actions ----------------

Tick ==
    /\ clock < MaxTime
    /\ clock' = clock + 1
    \* checkpoints whose lease expires are aborted
    /\ checkpointing' = [n \in Node |->
                            checkpointing[n] /\ clock + 1 < LatestLease(KnownCommitted(n)).exp]
    /\ UNCHANGED <<alive, connected, failures, paxosVars, lastCkpt, ckptDone>>

Crash(n) ==
    /\ alive[n]
    /\ failures < MaxFailures
    /\ alive' = [alive EXCEPT ![n] = FALSE]
    /\ failures' = failures + 1
    /\ leader' = IF leader = n THEN NoNode ELSE leader
    /\ checkpointing' = [checkpointing EXCEPT ![n] = FALSE]
    /\ UNCHANGED <<connected, clock, logs, chosen, commitIdx, lastCkpt, ckptDone>>

Recover(n) ==
    /\ ~alive[n]
    /\ alive' = [alive EXCEPT ![n] = TRUE]
    /\ UNCHANGED <<connected, clock, failures, paxosVars, ckptVars>>

Disconnect(n) ==
    /\ connected[n]
    /\ failures < MaxFailures
    /\ connected' = [connected EXCEPT ![n] = FALSE]
    /\ failures' = failures + 1
    /\ leader' = IF leader = n THEN NoNode ELSE leader
    /\ UNCHANGED <<alive, clock, logs, chosen, commitIdx, ckptVars>>

Reconnect(n) ==
    /\ ~connected[n]
    /\ connected' = [connected EXCEPT ![n] = TRUE]
    /\ UNCHANGED <<alive, clock, failures, paxosVars, ckptVars>>

\* ---------------- Paxos actions ----------------

\* Leader election: abstracts a successful Paxos ballot; a winning candidate's
\* log necessarily contains every chosen entry (quorum intersection).
ElectLeader(n) ==
    /\ leader = NoNode
    /\ Reachable(n)
    /\ Extends(logs[n], chosen)
    /\ leader' = n
    /\ commitIdx' = [commitIdx EXCEPT ![n] = Len(chosen)]
    /\ UNCHANGED <<envVars, logs, chosen, ckptVars>>

\* Leader proposes a client request
ProposeRequest(l) ==
    /\ leader = l
    /\ Reachable(l)
    /\ Len(logs[l]) < MaxLogLen
    /\ logs' = [logs EXCEPT ![l] = Append(@, ReqEntry)]
    /\ UNCHANGED <<envVars, leader, chosen, commitIdx, ckptVars>>

\* Leader proposes a checkpoint lease for eligible node n, only once the
\* previous lease (as seen in its own log) has expired.
GrantLease(l, n) ==
    /\ leader = l
    /\ Reachable(l)
    /\ n # l
    /\ alive[n]
    /\ Len(logs[l]) < MaxLogLen
    /\ LatestLease(logs[l]).exp <= clock
    /\ logs' = [logs EXCEPT ![l] =
                   Append(@, [type |-> "lease", owner |-> n, exp |-> clock + LeaseDuration])]
    /\ UNCHANGED <<envVars, leader, chosen, commitIdx, ckptVars>>

\* Leader replicates a prefix of its log to follower f (overwriting conflicts)
Replicate(l, f) ==
    /\ leader = l
    /\ f # l
    /\ Reachable(l)
    /\ Reachable(f)
    /\ \E k \in commitIdx[f]..Len(logs[l]) :
          /\ SubSeq(logs[l], 1, k) # logs[f]
          /\ logs' = [logs EXCEPT ![f] = SubSeq(logs[l], 1, k)]
          /\ commitIdx' = [commitIdx EXCEPT ![f] = Min(k, Len(chosen))]
    /\ UNCHANGED <<envVars, leader, chosen, ckptVars>>

\* Leader commits a prefix once a majority stores it
Commit(l) ==
    /\ leader = l
    /\ Reachable(l)
    /\ \E k \in (Len(chosen)+1)..Len(logs[l]) :
          /\ IsMajority({n \in Node : Extends(logs[n], SubSeq(logs[l], 1, k))})
          /\ chosen' = SubSeq(logs[l], 1, k)
          /\ commitIdx' = [commitIdx EXCEPT ![l] = k]
    /\ UNCHANGED <<envVars, leader, logs, ckptVars>>

\* ---------------- Checkpoint actions ----------------

StartCheckpoint(n) ==
    /\ alive[n]
    /\ ~checkpointing[n]
    /\ HoldsLease(n)
    /\ checkpointing' = [checkpointing EXCEPT ![n] = TRUE]
    /\ UNCHANGED <<envVars, paxosVars, lastCkpt, ckptDone>>

CompleteCheckpoint(n) ==
    /\ alive[n]
    /\ checkpointing[n]
    /\ HoldsLease(n)
    /\ checkpointing' = [checkpointing EXCEPT ![n] = FALSE]
    /\ lastCkpt' = [lastCkpt EXCEPT ![n] = commitIdx[n]]
    /\ ckptDone' = ckptDone \cup {n}
    /\ UNCHANGED <<envVars, paxosVars>>

-----------------------------------------------------------------------------------------
Next ==
    \/ Tick
    \/ \E n \in Node :
          \/ Crash(n) \/ Recover(n) \/ Disconnect(n) \/ Reconnect(n)
          \/ ElectLeader(n) \/ ProposeRequest(n) \/ Commit(n)
          \/ StartCheckpoint(n) \/ CompleteCheckpoint(n)
    \/ \E l, n \in Node : GrantLease(l, n) \/ Replicate(l, n)

Fairness ==
    /\ WF_vars(Tick)
    /\ \A n \in Node :
          /\ WF_vars(Recover(n))
          /\ WF_vars(Reconnect(n))
          /\ WF_vars(ElectLeader(n))
          /\ WF_vars(Commit(n))
          /\ SF_vars(StartCheckpoint(n))
          /\ SF_vars(CompleteCheckpoint(n))
    /\ \A l, n \in Node :
          /\ WF_vars(Replicate(l, n))
          /\ SF_vars(GrantLease(l, n))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------------------
\* ---------------- Invariants ----------------

TypeOK ==
    /\ alive \in [Node -> BOOLEAN]
    /\ connected \in [Node -> BOOLEAN]
    /\ clock \in 0..MaxTime
    /\ failures \in 0..MaxFailures
    /\ leader \in Node \cup {NoNode}
    /\ logs \in [Node -> Seq(Entry)]
    /\ \A n \in Node : Len(logs[n]) <= MaxLogLen
    /\ chosen \in Seq(Entry)
    /\ commitIdx \in [Node -> 0..MaxLogLen]
    /\ checkpointing \in [Node -> BOOLEAN]
    /\ lastCkpt \in [Node -> 0..MaxLogLen]
    /\ ckptDone \subseteq Node

\* At most one node holds a valid lease
LeaseExclusive ==
    \A m, n \in Node : HoldsLease(m) /\ HoldsLease(n) => m = n

\* Only the lease holder checkpoints, and at most one node at a time
CheckpointExclusive ==
    /\ \A n \in Node : checkpointing[n] => HoldsLease(n)
    /\ \A m, n \in Node : checkpointing[m] /\ checkpointing[n] => m = n

\* Logs never conflict on committed entries
LogConsistency ==
    /\ \A n \in Node :
          /\ commitIdx[n] <= Len(logs[n])
          /\ commitIdx[n] <= Len(chosen)
          /\ SubSeq(logs[n], 1, commitIdx[n]) = SubSeq(chosen, 1, commitIdx[n])
    /\ leader # NoNode => Extends(logs[leader], chosen)

Safety == LeaseExclusive /\ CheckpointExclusive /\ LogConsistency

\* ---------------- Liveness ----------------

\* A checkpoint opportunity (valid lease) eventually arises
CheckpointOpportunity == <>(\E n \in Node : HoldsLease(n))

\* Some checkpoint eventually completes
CheckpointCompletion == <>(ckptDone # {})

\* A started checkpoint eventually ends (completed or aborted)
CheckpointTerminates == \A n \in Node : checkpointing[n] ~> ~checkpointing[n]

THEOREM Spec => [](TypeOK /\ Safety)
THEOREM Spec => CheckpointOpportunity /\ CheckpointCompletion /\ CheckpointTerminates
=========================================================================================