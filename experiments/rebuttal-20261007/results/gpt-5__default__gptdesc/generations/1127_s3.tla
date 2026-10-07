------------------------------ MODULE TwoPhaseCommit ------------------------------

EXTENDS TLC

CONSTANTS RMs

ASSUME RMs # {}

RMState == {"working", "prepared", "committed", "aborted"}

VARIABLES rmState

vars == << rmState >>

Init ==
  rmState = [r \in RMs |-> "working"]

AllPrepared ==
  \A r \in RMs : rmState[r] = "prepared"

AnyCommitted ==
  \E r \in RMs : rmState[r] = "committed"

AbortAllowed ==
  ~AnyCommitted

Prepare(r) ==
  /\ r \in RMs
  /\ rmState[r] = "working"
  /\ rmState' = [rmState EXCEPT ![r] = "prepared"]

DecideCommit(r) ==
  /\ r \in RMs
  /\ rmState[r] = "prepared"
  /\ AllPrepared
  /\ rmState' = [rmState EXCEPT ![r] = "committed"]

DecideAbort(r) ==
  /\ r \in RMs
  /\ rmState[r] \in {"working", "prepared"}
  /\ AbortAllowed
  /\ rmState' = [rmState EXCEPT ![r] = "aborted"]

Decide(r) ==
  DecideCommit(r) \/ DecideAbort(r)

Next ==
  \E r \in RMs : Prepare(r) \/ Decide(r)

Spec ==
  Init /\ [][Next]_vars

TypeOK ==
  rmState \in [RMs -> RMState]

Consistency ==
  ~(\E r1 \in RMs : \E r2 \in RMs :
      rmState[r1] = "committed" /\ rmState[r2] = "aborted")

AlwaysTypeOK ==
  []TypeOK

AlwaysConsistency ==
  []Consistency

Safety ==
  AlwaysTypeOK /\ AlwaysConsistency

=============================================================================