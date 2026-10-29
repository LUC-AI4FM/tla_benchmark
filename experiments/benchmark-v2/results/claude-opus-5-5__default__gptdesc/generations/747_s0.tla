---------------------------- MODULE CheckpointCoordination ----------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
    Node,           \* set of replica nodes
    Nil,            \* distinguished "no node" value
    MaxLog,         \* bound on the length of the replicated log
    LeaseDuration   \* duration (in ticks) of a checkpoint lease

ASSUME /\ Nil \notin Node
       /\ Node # {}
       /\ MaxLog \in Nat \ {0}
       /\ LeaseDuration \in Nat \ {0}

VARIABLES
    \* ---------------- environment state ----------------
    up,             \* up[n] : node n is running
    connected,      \* connected[n] : node n is reachable over the network
    \* ---------------- Paxos / RSL state ----------------
    leader,         \* current primary (or Nil)
    ballot,         \* current ballot / view number
    chosen,         \* the sequence of decided (chosen) log entries
    log,            \* log[n] : the prefix of the decided log learned by n
    \* ---------------- checkpoint state -----------------
    leaseOwner,     \* node currently holding the checkpoint lease (or Nil)
    leaseTimer,     \* remaining lifetime of the checkpoint lease
    checkpointing,  \* checkpointing[n] : node n is currently taking a checkpoint
    lastCheckpoint  \* lastCheckpoint[n] : log index covered by n's latest checkpoint

envVars   == <<up, connected>>
paxosVars == <<leader, ballot, chosen, log>>
ckptVars  == <<leaseOwner, leaseTimer, checkpointing, lastCheckpoint>>
vars      == <<up, connected, leader, ballot, chosen, log,
               leaseOwner, leaseTimer, checkpointing, lastCheckpoint>>

-----------------------------------------------------------------------------------------
(* Helper definitions *)

Entry == [type : {"req", "lease"}, node : Node]

Quorum == {Q \in SUBSET Node : 2 * Cardinality(Q) > Cardinality(Node)}

Reachable(n) == up[n] /\ connected[n]

QuorumReachable == \E Q \in Quorum : \A m \in Q : Reachable(m)

LeaderActive == /\ leader # Nil
                /\ Reachable(leader)
                /\ QuorumReachable

Prefix(s, t) == /\ Len(s) <= Len(t)
                /\ SubSeq(t, 1, Len(s)) = s

\* Index of the most recent lease entry in the decided log (0 if none)
LastLeaseIdx ==
    IF \E i \in 1..Len(chosen) : chosen[i].type = "lease"
    THEN CHOOSE i \in 1..Len(chosen) :
            /\ chosen[i].type = "lease"
            /\ \A j \in (i+1)..Len(chosen) : chosen[j].type # "lease"
    ELSE 0

AnyCheckpointing == \E n \in Node : checkpointing[n]

-----------------------------------------------------------------------------------------
(* Type invariant *)

TypeOK ==
    /\ up \in [Node -> BOOLEAN]
    /\ connected \in [Node -> BOOLEAN]
    /\ leader \in Node \cup {Nil}
    /\ ballot \in Nat
    /\ chosen \in Seq(Entry)
    /\ Len(chosen) <= MaxLog
    /\ log \in [Node -> Seq(Entry)]
    /\ leaseOwner \in Node \cup {Nil}
    /\ leaseTimer \in 0..LeaseDuration
    /\ checkpointing \in [Node -> BOOLEAN]
    /\ lastCheckpoint \in [Node -> 0..MaxLog]

-----------------------------------------------------------------------------------------
(* Initial state *)

Init ==
    /\ up = [n \in Node |-> TRUE]
    /\ connected = [n \in Node |-> TRUE]
    /\ leader = Nil
    /\ ballot = 0
    /\ chosen = << >>
    /\ log = [n \in Node |-> << >>]
    /\ leaseOwner = Nil
    /\ leaseTimer = 0
    /\ checkpointing = [n \in Node |-> FALSE]
    /\ lastCheckpoint = [n \in Node |-> 0]

-----------------------------------------------------------------------------------------
(* Environment actions: node and network failures *)

NodeFail(n) ==
    /\ up[n]
    /\ up' = [up EXCEPT ![n] = FALSE]
    /\ leader' = IF leader = n THEN Nil ELSE leader
    /\ checkpointing' = [checkpointing EXCEPT ![n] = FALSE]
    /\ UNCHANGED <<connected, ballot, chosen, log,
                   leaseOwner, leaseTimer, lastCheckpoint>>

NodeRecover(n) ==
    /\ ~up[n]
    /\ up' = [up EXCEPT ![n] = TRUE]
    /\ UNCHANGED <<connected, paxosVars, ckptVars>>

NetFail(n) ==
    /\ connected[n]
    /\ connected' = [connected EXCEPT ![n] = FALSE]
    /\ leader' = IF leader = n THEN Nil ELSE leader
    /\ UNCHANGED <<up, ballot, chosen, log, ckptVars>>

NetRecover(n) ==
    /\ ~connected[n]
    /\ connected' = [connected EXCEPT ![n] = TRUE]
    /\ UNCHANGED <<up, paxosVars, ckptVars>>

-----------------------------------------------------------------------------------------
(* Paxos actions: leader election and replicated requests *)

\* A reachable node with a reachable quorum becomes primary; through phase 1
\* it learns every decided entry. A node in the middle of a checkpoint
\* is not eligible to become primary.
ElectLeader(n) ==
    /\ leader = Nil
    /\ Reachable(n)
    /\ QuorumReachable
    /\ ~checkpointing[n]
    /\ leader' = n
    /\ ballot' = ballot + 1
    /\ log' = [log EXCEPT ![n] = chosen]
    /\ UNCHANGED <<chosen, envVars, ckptVars>>

\* The primary replicates a client request.
ClientRequest ==
    /\ LeaderActive
    /\ Len(chosen) < MaxLog
    /\ LET e == [type |-> "req", node |-> leader]
       IN /\ chosen' = Append(chosen, e)
          /\ log' = [log EXCEPT ![leader] = Append(chosen, e)]
    /\ UNCHANGED <<leader, ballot, envVars, ckptVars>>

\* A secondary learns the next decided entry from the primary.
Replicate(n) ==
    /\ LeaderActive
    /\ n # leader
    /\ Reachable(n)
    /\ Len(log[n]) < Len(chosen)
    /\ log' = [log EXCEPT ![n] = SubSeq(chosen, 1, Len(log[n]) + 1)]
    /\ UNCHANGED <<leader, ballot, chosen, envVars, ckptVars>>

-----------------------------------------------------------------------------------------
(* Checkpoint actions: lease-based authorization *)

\* The primary grants the checkpoint lease to an eligible secondary by
\* replicating a lease entry, only once the previous lease has expired.
GrantLease(n) ==
    /\ LeaderActive
    /\ n # leader
    /\ Reachable(n)
    /\ leaseTimer = 0
    /\ ~AnyCheckpointing
    /\ Len(chosen) < MaxLog
    /\ LET e == [type |-> "lease", node |-> n]
       IN /\ chosen' = Append(chosen, e)
          /\ log' = [log EXCEPT ![leader] = Append(chosen, e)]
    /\ leaseOwner' = n
    /\ leaseTimer' = LeaseDuration
    /\ UNCHANGED <<leader, ballot, envVars, checkpointing, lastCheckpoint>>

\* A secondary starts checkpointing only if it holds a live lease and has
\* learned the lease entry through the replicated log.
StartCheckpoint(n) ==
    /\ up[n]
    /\ ~checkpointing[n]
    /\ n # leader
    /\ leaseOwner = n
    /\ leaseTimer > 0
    /\ LastLeaseIdx > 0
    /\ Len(log[n]) >= LastLeaseIdx
    /\ checkpointing' = [checkpointing EXCEPT ![n] = TRUE]
    /\ UNCHANGED <<envVars, paxosVars, leaseOwner, leaseTimer, lastCheckpoint>>

\* The checkpoint completes before lease expiry; the lease is released.
CompleteCheckpoint(n) ==
    /\ up[n]
    /\ checkpointing[n]
    /\ leaseTimer > 0
    /\ checkpointing' = [checkpointing EXCEPT ![n] = FALSE]
    /\ lastCheckpoint' = [lastCheckpoint EXCEPT ![n] = Len(log[n])]
    /\ leaseOwner' = Nil
    /\ leaseTimer' = 0
    /\ UNCHANGED <<envVars, paxosVars>>

\* Time passes; when the lease expires any in-progress checkpoint is aborted.
Tick ==
    /\ leaseTimer > 0
    /\ leaseTimer' = leaseTimer - 1
    /\ IF leaseTimer = 1
          THEN /\ checkpointing' = [n \in Node |-> FALSE]
               /\ leaseOwner' = Nil
          ELSE /\ UNCHANGED <<checkpointing, leaseOwner>>
    /\ UNCHANGED <<envVars, paxosVars, lastCheckpoint>>

-----------------------------------------------------------------------------------------
(* Next-state relation *)

EnvNext ==
    \E n \in Node : NodeFail(n) \/ NodeRecover(n) \/ NetFail(n) \/ NetRecover(n)

PaxosNext ==
    \/ \E n \in Node : ElectLeader(n)
    \/ ClientRequest
    \/ \E n \in Node : Replicate(n)

CheckpointNext ==
    \/ \E n \in Node : GrantLease(n)
    \/ \E n \in Node : StartCheckpoint(n)
    \/ \E n \in Node : CompleteCheckpoint(n)
    \/ Tick

Next == EnvNext \/ PaxosNext \/ CheckpointNext

-----------------------------------------------------------------------------------------
(* Fairness assumptions *)

Fairness ==
    /\ \A n \in Node : WF_vars(NodeRecover(n))
    /\ \A n \in Node : WF_vars(NetRecover(n))
    /\ \A n \in Node : WF_vars(ElectLeader(n))
    /\ \A n \in Node : WF_vars(Replicate(n))
    /\ \A n \in Node : SF_vars(GrantLease(n))
    /\ \A n \in Node : SF_vars(StartCheckpoint(n))
    /\ \A n \in Node : SF_vars(CompleteCheckpoint(n))
    /\ WF_vars(Tick)

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------------------
(* Safety *)

\* At most one node checkpoints at a time, only while holding a live lease,
\* and never the primary.
LeaseSafety ==
    /\ \A n, m \in Node : (checkpointing[n] /\ checkpointing[m]) => n = m
    /\ \A n \in Node : checkpointing[n] =>
          /\ leaseOwner = n
          /\ leaseTimer > 0
          /\ n # leader

\* Logs never conflict: every node's log is a prefix of the decided log,
\* and any two logs are prefix-comparable.
LogConsistency ==
    /\ \A n \in Node : Prefix(log[n], chosen)
    /\ \A n, m \in Node : Prefix(log[n], log[m]) \/ Prefix(log[m], log[n])

Safety == LeaseSafety /\ LogConsistency

-----------------------------------------------------------------------------------------
(* Liveness *)

\* A checkpoint opportunity (a granted lease) eventually arises.
EventuallyLeaseGranted == <>(leaseOwner # Nil)

\* Some node eventually starts a checkpoint.
EventuallyCheckpointStarts == <>AnyCheckpointing

\* Some checkpoint eventually completes.
EventuallyCheckpointCompletes == <>(\E n \in Node : lastCheckpoint[n] > 0)

\* Every started checkpoint eventually ends (completes or is aborted by expiry).
CheckpointTerminates ==
    \A n \in Node : checkpointing[n] ~> ~checkpointing[n]

Liveness ==
    /\ EventuallyLeaseGranted
    /\ EventuallyCheckpointStarts
    /\ EventuallyCheckpointCompletes
    /\ CheckpointTerminates

-----------------------------------------------------------------------------------------
THEOREM Spec => [](TypeOK /\ Safety)
THEOREM Spec => Liveness
=========================================================================================