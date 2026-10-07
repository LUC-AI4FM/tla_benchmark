---- MODULE TwoPhaseCommit ----
EXTENDS Naturals

CONSTANT RM

ASSUME RM /= {}

VARIABLES rmState

StateVals == {"working", "prepared", "committed", "aborted"}

TypeOK == rmState \in [RM -> StateVals]

Init == rmState = [r \in RM |-> "working"]

ExistsAborted == \E r \in RM : rmState[r] = "aborted"

AllPreparedOrCommitted == \A r \in RM : rmState[r] \in {"prepared", "committed"}

Prepare(r) ==
  /\ r \in RM
  /\ rmState[r] = "working"
  /\ ~ExistsAborted
  /\ rmState' = [rmState EXCEPT ![r] = "prepared"]

Decide(r) ==
  /\ r \in RM
  /\ ( \/ /\ rmState[r] = "working"
        /\ rmState' = [rmState EXCEPT ![r] = "aborted"]
     \/ /\ rmState[r] = "prepared"
        /\ ExistsAborted
        /\ rmState' = [rmState EXCEPT ![r] = "aborted"]
     \/ /\ rmState[r] = "prepared"
        /\ AllPreparedOrCommitted
        /\ rmState' = [rmState EXCEPT ![r] = "committed"]
     )

Next == \E r \in RM : Prepare(r) \/ Decide(r)

Consistency ==
  ~ ( (\E r \in RM : rmState[r] = "committed")
      /\ (\E r \in RM : rmState[r] = "aborted") )

vars == << rmState >>

Spec == Init /\ [][Next]_vars

THEOREM Spec => []TypeOK
THEOREM Spec => []Consistency

====