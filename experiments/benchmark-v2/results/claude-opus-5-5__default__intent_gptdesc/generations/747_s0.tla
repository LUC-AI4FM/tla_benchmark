---------------------------- MODULE CheckpointCoordination ----------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Node,      \* set of replica identifiers
          Nil,       \* distinguished "no node" value
          MaxLog     \* bound on log length (for finite model checking)

ASSUME Nil \notin Node
ASSUME MaxLog \in Nat /\ MaxLog > 0

VARIABLES up,        \* up[n]        : node n is alive
          link,      \* link[i][j]   : network link between i and j is working
          log,       \* log[n]       : replicated log held by n
          exec,      \* exec[n]      : execution counter (number of executed entries)
          leader,    \* current leader or Nil
          assigned,  \* assigned[n]  : checkpointer n has learned from executed log
          lease,     \* checkpoint lease: holder and the log counter it covers
          phase,     \* phase[n] \in {"idle","eligible","checkpointing"}
          snapshot   \* snapshot[n]  : last persisted checkpoint (log prefix, counter)

vars == <<up, link, log, exec, leader, assigned, lease, phase, snapshot>>

-----------------------------------------------------------------------------------------
Entry      == [kind : {"noop", "ckpt"}, target : Node \cup {Nil}, index : 1..MaxLog]
NoLease    == [holder |-> Nil, counter |-> 0]
BlankSnap  == [log |-> << >>, counter |-> 0]

Prefix(s, t) == Len(s) <= Len(t) /\ s = SubSeq(t, 1, Len(s))

Reachable(n) == {m \in Node : up[m] /\ (m = n \/ link[n][m])}
HasQuorum(n) == 2 * Cardinality(Reachable(n)) > Cardinality(Node)

\* Fully caught up: no pending (unexecuted) entries and no other replica holds a longer log
CaughtUp(n) == /\ exec[n] = Len(log[n])
               /\ \A m \in Node : Len(log[m]) <= Len(log[n])

Busy(n) == phase[n] \in {"eligible", "checkpointing"}

-----------------------------------------------------------------------------------------
TypeOK ==
    /\ up \in [Node -> BOOLEAN]
    /\ link \in [Node -> [Node -> BOOLEAN]]
    /\ \A n \in Node : log[n] \in Seq(Entry) /\ Len(log[n]) <= MaxLog
    /\ exec \in [Node -> 0..MaxLog]
    /\ leader \in Node \cup {Nil}
    /\ assigned \in [Node -> Node \cup {Nil}]
    /\ lease \in [holder : Node \cup {Nil}, counter : 0..MaxLog]
    /\ phase \in [Node -> {"idle", "eligible", "checkpointing"}]
    /\ \A n \in Node : snapshot[n].counter \in 0..MaxLog
                       /\ snapshot[n].log \in Seq(Entry)

Init ==
    /\ up = [n \in Node |-> TRUE]
    /\ link = [i \in Node |-> [j \in Node |-> TRUE]]
    /\ log = [n \in Node |-> << >>]
    /\ exec = [n \in Node |-> 0]
    /\ leader = Nil
    /\ assigned = [n \in Node |-> Nil]
    /\ lease = NoLease
    /\ phase = [n \in Node |-> "idle"]
    /\ snapshot = [n \in Node |-> BlankSnap]

-----------------------------------------------------------------------------------------
\* Failures and recoveries of nodes
Fail(n) ==
    /\ up[n]
    /\ up' = [up EXCEPT ![n] = FALSE]
    /\ phase' = [phase EXCEPT ![n] = "idle"]          \* failure preempts checkpointing
    /\ leader' = IF leader = n THEN Nil ELSE leader
    /\ UNCHANGED <<link, log, exec, assigned, lease, snapshot>>

Recover(n) ==
    /\ ~up[n]
    /\ up' = [up EXCEPT ![n] = TRUE]
    /\ UNCHANGED <<link, log, exec, leader, assigned, lease, phase, snapshot>>

\* Failures and recoveries of network links (symmetric)
LinkFail(i, j) ==
    /\ i # j /\ link[i][j]
    /\ link' = [link EXCEPT ![i][j] = FALSE, ![j][i] = FALSE]
    /\ UNCHANGED <<up, log, exec, leader, assigned, lease, phase, snapshot>>

LinkRecover(i, j) ==
    /\ i # j /\ ~link[i][j]
    /\ link' = [link EXCEPT ![i][j] = TRUE, ![j][i] = TRUE]
    /\ UNCHANGED <<up, log, exec, leader, assigned, lease, phase, snapshot>>

\* Leader election: requires quorum and being fully caught up
BecomeLeader(n) ==
    /\ leader = Nil
    /\ up[n]
    /\ HasQuorum(n)
    /\ CaughtUp(n)
    /\ phase[n] = "idle"
    /\ lease.holder # n
    /\ leader' = n
    /\ UNCHANGED <<up, link, log, exec, assigned, lease, phase, snapshot>>

StepDown(n) ==
    /\ leader = n
    /\ ~HasQuorum(n)
    /\ leader' = Nil
    /\ UNCHANGED <<up, link, log, exec, assigned, lease, phase, snapshot>>

\* Leader appends an ordinary command
ProposeNoop(n) ==
    /\ leader = n /\ up[n]
    /\ Len(log[n]) < MaxLog
    /\ log' = [log EXCEPT ![n] =
                 Append(@, [kind |-> "noop", target |-> Nil, index |-> Len(@) + 1])]
    /\ UNCHANGED <<up, link, exec, leader, assigned, lease, phase, snapshot>>

\* Leader proposes that non-leader replica t checkpoint at the current open log index
ProposeCheckpoint(n, t) ==
    /\ leader = n /\ up[n]
    /\ t # n
    /\ Len(log[n]) < MaxLog
    /\ log' = [log EXCEPT ![n] =
                 Append(@, [kind |-> "ckpt", target |-> t, index |-> Len(@) + 1])]
    /\ UNCHANGED <<up, link, exec, leader, assigned, lease, phase, snapshot>>

\* Dissemination: any up replica forwards its next entry to a reachable lagging replica,
\* so a replica that missed the original message can still learn it.
Replicate(i, j) ==
    /\ i # j
    /\ up[i] /\ up[j] /\ link[i][j]
    /\ Len(log[j]) < Len(log[i])
    /\ Prefix(log[j], log[i])
    /\ log' = [log EXCEPT ![j] = Append(@, log[i][Len(log[j]) + 1])]
    /\ UNCHANGED <<up, link, exec, leader, assigned, lease, phase, snapshot>>

\* Execute next log entry; monotonically increases the execution counter
Execute(n) ==
    /\ up[n]
    /\ exec[n] < Len(log[n])
    /\ LET e == log[n][exec[n] + 1] IN
         assigned' = IF e.kind = "ckpt"
                       THEN [assigned EXCEPT ![n] = e.target]
                       ELSE assigned
    /\ exec' = [exec EXCEPT ![n] = @ + 1]
    /\ UNCHANGED <<up, link, log, leader, lease, phase, snapshot>>

\* Lease acquisition by the assigned replica
AcquireLease(n) ==
    /\ up[n]
    /\ lease.holder = Nil
    /\ assigned[n] = n
    /\ leader # n
    /\ lease' = [holder |-> n, counter |-> exec[n]]
    /\ UNCHANGED <<up, link, log, exec, leader, assigned, phase, snapshot>>

\* Lease timeout: lease is released and its holder (if active) is preempted
LeaseTimeout ==
    /\ lease.holder # Nil
    /\ lease' = NoLease
    /\ phase' = [phase EXCEPT ![lease.holder] = "idle"]
    /\ UNCHANGED <<up, link, log, exec, leader, assigned, snapshot>>

\* Checkpointing node reports progress: lease replaced with a fresher counter
ReportProgress(n) ==
    /\ up[n]
    /\ phase[n] = "checkpointing"
    /\ lease.holder = n
    /\ exec[n] > lease.counter
    /\ lease' = [holder |-> n, counter |-> exec[n]]
    /\ UNCHANGED <<up, link, log, exec, leader, assigned, phase, snapshot>>

\* Node marks itself able to checkpoint
MarkEligible(n) ==
    /\ up[n]
    /\ phase[n] = "idle"
    /\ lease.holder = n
    /\ assigned[n] = n
    /\ leader # n
    /\ \A m \in Node \ {n} : ~Busy(m)
    /\ phase' = [phase EXCEPT ![n] = "eligible"]
    /\ UNCHANGED <<up, link, log, exec, leader, assigned, lease, snapshot>>

\* Begin checkpointing, mutually exclusive with other nodes
BeginCheckpoint(n) ==
    /\ up[n]
    /\ phase[n] = "eligible"
    /\ lease.holder = n
    /\ leader # n
    /\ \A m \in Node \ {n} : phase[m] # "checkpointing"
    /\ phase' = [phase EXCEPT ![n] = "checkpointing"]
    /\ UNCHANGED <<up, link, log, exec, leader, assigned, lease, snapshot>>

\* Complete checkpoint: persist snapshot (log prefix, counter) and clear the lease
CompleteCheckpoint(n) ==
    /\ up[n]
    /\ phase[n] = "checkpointing"
    /\ lease.holder = n
    /\ snapshot' = [snapshot EXCEPT ![n] =
                      [log |-> SubSeq(log[n], 1, exec[n]), counter |-> exec[n]]]
    /\ lease' = NoLease
    /\ phase' = [phase EXCEPT ![n] = "idle"]
    /\ UNCHANGED <<up, link, log, exec, leader, assigned>>

-----------------------------------------------------------------------------------------
Next ==
    \/ \E n \in Node : Fail(n) \/ Recover(n)
    \/ \E i, j \in Node : LinkFail(i, j) \/ LinkRecover(i, j)
    \/ \E n \in Node : BecomeLeader(n) \/ StepDown(n)
    \/ \E n \in Node : ProposeNoop(n)
    \/ \E n, t \in Node : ProposeCheckpoint(n, t)
    \/ \E i, j \in Node : Replicate(i, j)
    \/ \E n \in Node : Execute(n)
    \/ \E n \in Node : AcquireLease(n)
    \/ LeaseTimeout
    \/ \E n \in Node : ReportProgress(n)
    \/ \E n \in Node : MarkEligible(n)
    \/ \E n \in Node : BeginCheckpoint(n)
    \/ \E n \in Node : CompleteCheckpoint(n)

Fairness ==
    /\ \A n \in Node : WF_vars(Recover(n))
    /\ \A i, j \in Node : WF_vars(LinkRecover(i, j))
    /\ \A n \in Node : WF_vars(BecomeLeader(n))
    /\ \A n \in Node : WF_vars(\E t \in Node : ProposeCheckpoint(n, t))
    /\ \A i, j \in Node : WF_vars(Replicate(i, j))
    /\ \A n \in Node : WF_vars(Execute(n))
    /\ \A n \in Node : WF_vars(AcquireLease(n))
    /\ \A n \in Node : WF_vars(MarkEligible(n))
    /\ \A n \in Node : WF_vars(BeginCheckpoint(n))
    /\ \A n \in Node : WF_vars(CompleteCheckpoint(n))
    /\ WF_vars(LeaseTimeout)

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------------------
\* Safety properties

\* At most one node is eligible or actively checkpointing at once
AtMostOneCheckpointer ==
    \A m, n \in Node : (Busy(m) /\ Busy(n)) => m = n

\* The leader never itself takes a checkpoint
LeaderNeverCheckpoints ==
    leader # Nil => phase[leader] = "idle"

\* Leases imply exclusivity: any active node holds the (unique) lease
LeaseExclusivity ==
    \A n \in Node : Busy(n) => lease.holder = n

\* Replicated logs never contain conflicting entries
NoConflictingLogs ==
    \A i, j \in Node : Prefix(log[i], log[j]) \/ Prefix(log[j], log[i])

\* Execution counter never exceeds log length
ExecWithinLog ==
    \A n \in Node : exec[n] <= Len(log[n])

\* Execution counters increase monotonically
ExecMonotonic ==
    [][\A n \in Node : exec'[n] >= exec[n]]_vars

Safety ==
    /\ TypeOK
    /\ AtMostOneCheckpointer
    /\ LeaderNeverCheckpoints
    /\ LeaseExclusivity
    /\ NoConflictingLogs
    /\ ExecWithinLog

-----------------------------------------------------------------------------------------
\* Liveness properties

EventuallyEligible ==
    <>(\E n \in Node : phase[n] = "eligible")

EligibleEventuallyStarts ==
    \A n \in Node :
        (phase[n] = "eligible") ~>
            (phase[n] = "checkpointing" \/ ~up[n] \/ lease.holder # n)

CheckpointingEventuallyEnds ==
    \A n \in Node :
        (phase[n] = "checkpointing") ~>
            (phase[n] # "checkpointing" \/ lease.holder # n \/ ~up[n])

EventuallyNonBlankCheckpoint ==
    <>(\E n \in Node : snapshot[n].counter > 0)

Liveness ==
    /\ EventuallyEligible
    /\ EligibleEventuallyStarts
    /\ CheckpointingEventuallyEnds
    /\ EventuallyNonBlankCheckpoint

THEOREM Spec => []Safety
=========================================================================================