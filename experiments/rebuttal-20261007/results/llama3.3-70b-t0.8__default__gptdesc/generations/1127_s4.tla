```
MODULE TwoPhaseCommit
EXTENDS Integers, TLC

CONSTANTS NumRMs
VARIABLES rmState

Init == (rmState = [i \in 1..NumRMs |-> "working"])

Prepare(rm) == 
  IF rmState[rm] = "working" THEN
    rmState' = [rmState EXCEPT ![rm] = "prepared"]
  ELSE
    UNCHANGED rmState

Decide(rm, outcome) == 
  IF rmState[rm] = "prepared" THEN
    IF outcome = "commit" THEN
      rmState' = [rmState EXCEPT ![rm] = "committed"]
    ELSE
      rmState' = [rmState EXCEPT ![rm] = "aborted"]
  ELSE
    UNCHANGED rmState

Next == \E rm \in 1..NumRMs : 
          (Prepare(rm)) \/ (\E outcome \in {"commit", "abort"} : Decide(rm, outcome))

Spec == Init /\ [][Next]_rmState

TypeCorrectness == rmState \in [1..NumRMs -> {"working", "prepared", "committed", "aborted"}]

Consistency == \A rm1, rm2 \in 1..NumRMs : 
                 ~(rmState[rm1] = "committed" /\ rmState[rm2] = "aborted")

SafetyInvariant == TypeCorrectness /\ Consistency

THEOREM Spec => []SafetyInvariant
```