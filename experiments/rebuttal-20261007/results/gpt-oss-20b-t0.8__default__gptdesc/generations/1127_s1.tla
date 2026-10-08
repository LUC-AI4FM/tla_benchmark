--------------------------- MODULE TwoPhaseCommit ----------------------------
EXTENDS Naturals, TLC

CONSTANTS RMs

VARIABLE rmState

States == {"working", "prepared", "committed", "aborted"}

Init ==
  /\ rmState \in [RMs -> States]
  /\ \A r \in RMs : rmState[r] = "working"

Prepare(r) ==
  /\ r \in RMs
  /\ rmState[r] = "working"
  /\ rmState' = [rmState EXCEPT ![r] = "prepared"]

DecideCommit(r) ==
  /\ r \in RMs
  /\ rmState[r] = "prepared"
  /\ rmState' = [rmState EXCEPT ![r] = "committed"]

DecideAbort(r) ==
  /\ r \in RMs
  /\ rmState[r] = "prepared"
  /\ rmState' = [rmState EXCEPT ![r] = "aborted"]

Next == \E r \in RMs : Prepare(r) \/ DecideCommit(r) \/ DecideAbort(r)

TypeCorrectness ==
  rmState \in [RMs -> States]

ConsistencyInvariant ==
  ~(\E r1 r2 \in RMs :
      /\ rmState[r1] = "committed"
      /\ rmState[r2] = "aborted")

Spec == Init /\ [][Next]_rmState

SafetyInvariant == TypeCorrectness /\ ConsistencyInvariant
===============================================================================