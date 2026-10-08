---------------------------- MODULE SinglePhaseAtomicCommit ----------------------------

EXTENDS Naturals

CONSTANT RM
ASSUME RM = 1..3

VARIABLES rmState

States == {"working", "prepared", "committed", "aborted"}
WorkingOrPrepared == {"working", "prepared"}
PreparedOrCommitted == {"prepared", "committed"}

TypeOK == rmState \in [RM -> States]

Consistency ==
  ~(\E r1 \in RM: \E r2 \in RM:
      rmState[r1] = "committed" /\ rmState[r2] = "aborted")

NoDecisionYet == \A r \in RM: rmState[r] \in WorkingOrPrepared
AllPreparedOrCommitted == \A r \in RM: rmState[r] \in PreparedOrCommitted

Init == rmState = [r \in RM |-> "working"]

Prepare(r) ==
  /\ r \in RM
  /\ NoDecisionYet
  /\ rmState[r] = "working"
  /\ rmState' = [rmState EXCEPT ![r] = "prepared"]

Abort(r) ==
  /\ r \in RM
  /\ NoDecisionYet
  /\ rmState[r] \in WorkingOrPrepared
  /\ rmState' = [rmState EXCEPT ![r] = "aborted"]

Commit(r) ==
  /\ r \in RM
  /\ rmState[r] = "prepared"
  /\ AllPreparedOrCommitted
  /\ rmState' = [rmState EXCEPT ![r] = "committed"]

Next ==
  \E r \in RM: Prepare(r) \/ Abort(r) \/ Commit(r)

vars == << rmState >>

Spec == Init /\ [][Next]_vars

================================================================================