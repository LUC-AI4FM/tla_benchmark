------------------------------- MODULE CheckpointCoordination -------------------------------
(***************************************************************************)
(* Checkpoint coordination in a replicated Paxos/RSL-style cluster.        *)
(*                                                                         *)
(* The state is split into three groups:                                   *)
(*   - Environment state: node liveness, network connectivity, a global    *)
(*     clock and a bounded failure budget.                                 *)
(*   - Paxos state: ballots/terms, roles, replicated logs and commit       *)
(*     indices.                                                            *)
(*   - Checkpoint state: which nodes are checkpointing, the expiry of the  *)
(*     lease each one is using, and the last checkpointed log index.       *)
(*                                                                         *)
(* A leader replicates client requests and checkpoint-lease entries. A     *)
(* non-leader node may checkpoint only while it holds an unexpired lease   *)
(* that is recorded in a committed log entry. A leader grants a new lease  *)
(* only when no lease in its log is still active. This ensures that at     *)
(* most one eligible node checkpoints at a time, and that committed logs   *)
(* do not conflict.                                                        *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
    Node,           \* set of replica identifiers
    MaxTerm,        \* bound on terms/ballots
    MaxLogLen,      \* bound on the length of the replicated log
    MaxTime,        \* bound on the global clock
    LeaseDuration,  \* duration of a checkpoint lease
    MaxFailures     \* bound on the number of node/network failures

ASSUME /\ Node # {}
       /\ MaxTerm \in Nat \ {0}
       /\ MaxLogLen \in Nat \ {0}
       /\ MaxTime \in Nat \ {0}
       /\ LeaseDuration \in Nat \ {0}
       /\ MaxFailures \in Nat

NoNode == CHOOSE x : x \notin Node

-----------------------------------------------------------------------------
(* Environment state *)
VARIABLES
    nodeUp,       \* nodeUp[n]   : node n is running
    netUp,        \* netUp[n]    : node n is connected to the network
    now,          \* global clock
    failures      \* number of failures injected so far

(* Paxos-related state *)
VARIABLES
    term,         \* term[n]        : current term (ballot) of node n
    role,         \* role[n]        : "Leader" or "Follower"
    log,          \* log[n]         : replicated log at node n
    commitIndex   \* commitIndex[n] : highest log index known committed at n

(* Checkpoint-specific state *)
VARIABLES
    checkpointing, \* checkpointing[n] : node n is currently checkpointing
    ckptLeaseExp,  \* ckptLeaseExp[n]  : expiry of the lease n checkpoints under
    lastCkpt       \* lastCkpt[n]      : last log index captured in a checkpoint

envVars   == <<nodeUp, netUp, now, failures>>
paxosVars == <<term, role, log, commitIndex>>
ckptVars  == <<checkpointing, ckptLeaseExp, lastCkpt>>
vars      == <<envVars, paxosVars, ckptVars>>

-----------------------------------------------------------------------------
(* Helpers *)

Entry == [term   : 0..MaxTerm,
          type   : {"Request", "Lease"},
          holder : Node \cup {NoNode},
          expiry : 0..(MaxTime + LeaseDuration)]

NoLeaseEntry == [term |-> 0, type |-> "Lease", holder |-> NoNode, expiry |-> 0]

Min(a, b) == IF a <= b THEN a ELSE b

MaxSet(S) == CHOOSE x \in S : \A y \in S : y <= x

Quorum == {Q \in SUBSET Node : 2 * Cardinality(Q) > Cardinality(Node)}

LastTerm(s) == IF Len(s) = 0 THEN 0 ELSE s[Len(s)].term

\* log a is at least as up to date as log b
UpToDate(a, b) == \/ LastTerm(a) > LastTerm(b)
                  \/ /\ LastTerm(a) = LastTerm(b)
                     /\ Len(a) >= Len(b)

CanCommunicate(a, b) == /\ nodeUp[a] /\ nodeUp[b]
                        /\ netUp[a]  /\ netUp[b]

LeaseIdx(lg, k) == {i \in 1..k : lg[i].type = "Lease"}

\* The most recent committed lease entry known at node n
CurrentLease(n) ==
    LET S == LeaseIdx(log[n], commitIndex[n])
    IN  IF S = {} THEN NoLeaseEntry ELSE log[n][MaxSet(S)]

\* No lease entry in the leader's log (committed or not) is still active
NoActiveLeaseIn(lg) ==
    \A i \in 1..Len(lg) : lg[i].type = "Lease" => lg[i].expiry <= now

\* Node n is eligible and authorized to start a checkpoint
CanStartCheckpoint(n) ==
    /\ nodeUp[n]
    /\ role[n] = "Follower"
    /\ ~checkpointing[n]
    /\ CurrentLease(n).holder = n
    /\ CurrentLease(n).expiry > now

-----------------------------------------------------------------------------
Init ==
    \* environment
    /\ nodeUp = [n \in Node |-> TRUE]
    /\ netUp = [n \in Node |-> TRUE]
    /\ now = 0
    /\ failures = 0
    \* paxos
    /\ term = [n \in Node |-> 0]
    /\ role = [n \in Node |-> "Follower"]
    /\ log = [n \in Node |-> << >>]
    /\ commitIndex = [n \in Node |-> 0]
    \* checkpoint
    /\ checkpointing = [n \in Node |-> FALSE]
    /\ ckptLeaseExp = [n \in Node |-> 0]
    /\ lastCkpt = [n \in Node |-> 0]

-----------------------------------------------------------------------------
(* Environment actions *)

\* Time advances; any checkpoint whose lease expires is aborted.
Tick ==
    /\ now < MaxTime
    /\ now' = now + 1
    /\ checkpointing' = [n \in Node |->
                            checkpointing[n] /\ ckptLeaseExp[n] > now + 1]
    /\ UNCHANGED <<nodeUp, netUp, failures, paxosVars, ckptLeaseExp, lastCkpt>>

NodeCrash(n) ==
    /\ nodeUp[n]
    /\ failures < MaxFailures
    /\ failures' = failures + 1
    /\ nodeUp' = [nodeUp EXCEPT ![n] = FALSE]
    /\ role' = [role EXCEPT ![n] = "Follower"]
    /\ checkpointing' = [checkpointing EXCEPT ![n] = FALSE]
    /\ UNCHANGED <<netUp, now, term, log, commitIndex, ckptLeaseExp, lastCkpt>>

NodeRecover(n) ==
    /\ ~nodeUp[n]
    /\ nodeUp' = [nodeUp EXCEPT ![n] = TRUE]
    /\ UNCHANGED <<netUp, now, failures, paxosVars, ckptVars>>

NetFail(n) ==
    /\ netUp[n]
    /\ failures < MaxFailures
    /\ failures' = failures + 1
    /\ netUp' = [netUp EXCEPT ![n] = FALSE]
    /\ UNCHANGED <<nodeUp, now, paxosVars, ckptVars>>

NetRecover(n) ==
    /\ ~netUp[n]
    /\ netUp' = [netUp EXCEPT ![n] = TRUE]
    /\ UNCHANGED <<nodeUp, now, failures, paxosVars, ckptVars>>

-----------------------------------------------------------------------------
(* Paxos actions *)

\* Node n wins an election with quorum Q
BecomeLeader(n, Q) ==
    LET newTerm == MaxSet({term[q] : q \in Q}) + 1
    IN
    /\ n \in Q
    /\ \A q \in Q : CanCommunicate(n, q)
    /\ newTerm <= MaxTerm
    /\ \A q \in Q : UpToDate(log[n], log[q])
    /\ term' = [m \in Node |-> IF m \in Q THEN newTerm ELSE term[m]]
    /\ role' = [m \in Node |-> IF m = n THEN "Leader"
                               ELSE IF m \in Q THEN "Follower"
                               ELSE role[m]]
    /\ checkpointing' = [checkpointing EXCEPT ![n] = FALSE]
    /\ UNCHANGED <<envVars, log, commitIndex, ckptLeaseExp, lastCkpt>>

\* A stale leader learns of a higher term and steps down
StepDown(n, m) ==
    /\ role[n] = "Leader"
    /\ CanCommunicate(n, m)
    /\ term[m] > term[n]
    /\ term' = [term EXCEPT ![n] = term[m]]
    /\ role' = [role EXCEPT ![n] = "Follower"]
    /\ UNCHANGED <<envVars, log, commitIndex, ckptVars>>

\* Leader appends a replicated client request
ClientRequest(l) ==
    /\ role[l] = "Leader"
    /\ nodeUp[l]
    /\ Len(log[l]) < MaxLogLen
    /\ log' = [log EXCEPT ![l] =
                 Append(@, [term |-> term[l], type |-> "Request",
                            holder |-> NoNode, expiry |-> 0])]
    /\ UNCHANGED <<envVars, term, role, commitIndex, ckptVars>>

\* Leader appends a checkpoint-lease entry for an eligible node h
GrantLease(l, h) ==
    /\ role[l] = "Leader"
    /\ nodeUp[l]
    /\ h \in Node \ {l}
    /\ Len(log[l]) < MaxLogLen
    /\ NoActiveLeaseIn(log[l])
    /\ log' = [log EXCEPT ![l] =
                 Append(@, [term |-> term[l], type |-> "Lease",
                            holder |-> h, expiry |-> now + LeaseDuration])]
    /\ UNCHANGED <<envVars, term, role, commitIndex, ckptVars>>

\* Leader replicates its log to follower f
Replicate(l, f) ==
    /\ l # f
    /\ role[l] = "Leader"
    /\ CanCommunicate(l, f)
    /\ term[f] <= term[l]
    /\ log' = [log EXCEPT ![f] = log[l]]
    /\ term' = [term EXCEPT ![f] = term[l]]
    /\ role' = [role EXCEPT ![f] = "Follower"]
    /\ commitIndex' = [commitIndex EXCEPT ![f] =
                          IF commitIndex[l] > commitIndex[f]
                          THEN commitIndex[l]
                          ELSE Min(commitIndex[f], Len(log[l]))]
    /\ UNCHANGED <<envVars, ckptVars>>

\* Leader commits index i once a quorum stores a matching prefix
Commit(l, i) ==
    /\ role[l] = "Leader"
    /\ nodeUp[l]
    /\ i \in (commitIndex[l] + 1)..Len(log[l])
    /\ log[l][i].term = term[l]
    /\ \E Q \in Quorum :
         \A q \in Q : /\ Len(log[q]) >= i
                      /\ SubSeq(log[q], 1, i) = SubSeq(log[l], 1, i)
    /\ commitIndex' = [commitIndex EXCEPT ![l] = i]
    /\ UNCHANGED <<envVars, term, role, log, ckptVars>>

-----------------------------------------------------------------------------
(* Checkpoint actions *)

StartCheckpoint(n) ==
    /\ CanStartCheckpoint(n)
    /\ checkpointing' = [checkpointing EXCEPT ![n] = TRUE]
    /\ ckptLeaseExp' = [ckptLeaseExp EXCEPT ![n] = CurrentLease(n).expiry]
    /\ UNCHANGED <<envVars, paxosVars, lastCkpt>>

CompleteCheckpoint(n) ==
    /\ checkpointing[n]
    /\ nodeUp[n]
    /\ ckptLeaseExp[n] > now
    /\ checkpointing' = [checkpointing EXCEPT ![n] = FALSE]
    /\ lastCkpt' = [lastCkpt EXCEPT ![n] = commitIndex[n]]
    /\ UNCHANGED <<envVars, paxosVars, ckptLeaseExp>>

-----------------------------------------------------------------------------
EnvNext ==
    \/ Tick
    \/ \E n \in Node : NodeCrash(n) \/ NodeRecover(n)
                       \/ NetFail(n) \/ NetRecover(n)

PaxosNext ==
    \/ \E n \in Node, Q \in Quorum : BecomeLeader(n, Q)
    \/ \E n, m \in Node : StepDown(n, m)
    \/ \E l \in Node : ClientRequest(l)
    \/ \E l, h \in Node : GrantLease(l, h)
    \/ \E l, f \in Node : Replicate(l, f)
    \/ \E l \in Node, i \in 1..MaxLogLen : Commit(l, i)

CkptNext ==
    \/ \E n \in Node : StartCheckpoint(n)
    \/ \E n \in Node : CompleteCheckpoint(n)

Next == EnvNext \/ PaxosNext \/ CkptNext

Fairness ==
    /\ WF_vars(Tick)
    /\ \A n \in Node : WF_vars(NodeRecover(n))
    /\ \A n \in Node : WF_vars(NetRecover(n))
    /\ SF_vars(\E n \in Node, Q \in Quorum : BecomeLeader(n, Q))
    /\ \A l, f \in Node : WF_vars(Replicate(l, f))
    /\ \A l \in Node : WF_vars(\E i \in 1..MaxLogLen : Commit(l, i))
    /\ SF_vars(\E l, h \in Node : GrantLease(l, h))
    /\ \A n \in Node : SF_vars(StartCheckpoint(n))
    /\ \A n \in Node : WF_vars(CompleteCheckpoint(n))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Invariants *)

TypeOK ==
    /\ nodeUp \in [Node -> BOOLEAN]
    /\ netUp \in [Node -> BOOLEAN]
    /\ now \in 0..MaxTime
    /\ failures \in 0..MaxFailures
    /\ term \in [Node -> 0..MaxTerm]
    /\ role \in [Node -> {"Leader", "Follower"}]
    /\ log \in [Node -> Seq(Entry)]
    /\ \A n \in Node : Len(log[n]) <= MaxLogLen
    /\ commitIndex \in [Node -> 0..MaxLogLen]
    /\ \A n \in Node : commitIndex[n] <= Len(log[n])
    /\ checkpointing \in [Node -> BOOLEAN]
    /\ ckptLeaseExp \in [Node -> 0..(MaxTime + LeaseDuration)]
    /\ lastCkpt \in [Node -> 0..MaxLogLen]

\* At most one node checkpoints at any time
LeaseExclusive ==
    \A n, m \in Node : (checkpointing[n] /\ checkpointing[m]) => n = m

\* A checkpointing node is an eligible (non-leader) holder of a live lease
CheckpointerHoldsLease ==
    \A n \in Node : checkpointing[n] =>
        /\ role[n] # "Leader"
        /\ ckptLeaseExp[n] > now

\* Committed log prefixes never conflict
LogConsistency ==
    \A n, m \in Node :
        \A i \in 1..Min(commitIndex[n], commitIndex[m]) :
            log[n][i] = log[m][i]

Safety == LeaseExclusive /\ CheckpointerHoldsLease /\ LogConsistency

-----------------------------------------------------------------------------
(* Temporal properties *)

\* Some node eventually gets an opportunity to checkpoint
CheckpointOpportunity == <>(\E n \in Node : CanStartCheckpoint(n))

\* Every started checkpoint eventually finishes (completed or aborted)
CheckpointTerminates == \A n \in Node : checkpointing[n] ~> ~checkpointing[n]

\* Some checkpoint is eventually completed
CheckpointCompletion == <>(\E n \in Node : lastCkpt[n] > 0)

THEOREM Spec => [](TypeOK /\ Safety)
=============================================================================