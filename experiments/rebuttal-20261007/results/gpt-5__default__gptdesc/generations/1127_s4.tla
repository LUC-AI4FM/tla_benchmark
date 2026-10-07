------------------------------ MODULE TwoPhaseCommit ------------------------------

EXTENDS TLC

CONSTANT RM

VARIABLE rmState

States == {"working", "prepared", "committed", "aborted"}

Init ==
  rmState = [r \in RM |-> "working"]

AllPreparedOrCommitted ==
  \A r \in RM: rmState[r] \in {"prepared", "committed"}

AnyCommitted ==
  \E r \in RM: rmState[r] = "committed"

Prepare(r) ==
  /\ r \in RM
  /\ rmState[r] = "working"
  /\ rmState' = [rmState EXCEPT ![r] = "prepared"]

DecideCommit(r) ==
  /\ r \in RM
  /\ rmState[r] = "prepared"
  /\ AllPreparedOrCommitted
  /\ rmState' = [rmState EXCEPT ![r] = "committed"]

DecideAbort(r) ==
  /\ r \in RM
  /\ rmState[r] \in {"working", "prepared"}
  /\ ~AnyCommitted
  /\ rmState' = [rmState EXCEPT ![r] = "aborted"]

Decide(r) ==
  DecideCommit(r) \/ DecideAbort(r)

Next ==
  \E r \in RM: Prepare(r) \/ Decide(r)

Spec ==
  Init /\ [][Next]_rmState

TypeOK ==
  rmState \in [RM -> States]

Consistency ==
  ~(\E r1 \in RM: \E r2 \in RM:
      /\ rmState[r1] = "committed"
      /\ rmState[r2] = "aborted")

SafetyInvariants ==
  TypeOK /\ Consistency

=============================================================================