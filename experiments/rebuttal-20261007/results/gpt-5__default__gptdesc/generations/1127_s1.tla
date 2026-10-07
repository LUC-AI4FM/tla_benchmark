--------------------------- MODULE TwoPhaseCommit ---------------------------

EXTENDS Naturals

CONSTANTS RMs

ASSUME RMs # {}

VARIABLES rmState

RMStates == {"working", "prepared", "committed", "aborted"}

TypeOK ==
  rmState \in [RMs -> RMStates]

Init ==
  /\ TypeOK
  /\ \A r \in RMs: rmState[r] = "working"

CanCommit ==
  \A r \in RMs: rmState[r] \in {"prepared", "committed"}

SomeCommitted ==
  \E r \in RMs: rmState[r] = "committed"

SomeAborted ==
  \E r \in RMs: rmState[r] = "aborted"

Prepare(r) ==
  /\ r \in RMs
  /\ rmState[r] = "working"
  /\ rmState' = [rmState EXCEPT ![r] = "prepared"]

DecideCommit(r) ==
  /\ r \in RMs
  /\ rmState[r] \in {"working", "prepared"}
  /\ CanCommit
  /\ ~SomeAborted
  /\ rmState' = [rmState EXCEPT ![r] = "committed"]

DecideAbort(r) ==
  /\ r \in RMs
  /\ rmState[r] \in {"working", "prepared"}
  /\ ~SomeCommitted
  /\ ~CanCommit
  /\ rmState' = [rmState EXCEPT ![r] = "aborted"]

Decide(r) ==
  DecideCommit(r) \/ DecideAbort(r)

Next ==
  \E r \in RMs: Prepare(r) \/ Decide(r)

Spec ==
  Init /\ [][Next]_rmState

\* Safety invariants
NoConflictingDecisions ==
  ~((\E r \in RMs: rmState[r] = "committed")
    /\ (\E r \in RMs: rmState[r] = "aborted"))

TypeInvariant == TypeOK

SafetyInvariant == TypeInvariant /\ NoConflictingDecisions

=============================================================================