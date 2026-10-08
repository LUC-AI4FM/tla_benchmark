```
MODULE TwoPhaseCommit
EXTENDS Integers, FiniteSets

CONSTANTS RMs
VARIABLES state

Init ==
  state = [r \in RMs |-> "working"]

Next ==
  /\ state' = [s \in state |-> IF s = "working" THEN "prepared"
                                  ELSE IF s = "prepared" THEN "committed"
                                  ELSE IF s = "prepared" THEN "aborted"
                                  ELSE s]
  \/ (\E r \in RMs : state[r] = "working" /\ state' = [state EXCEPT ![r] = "prepared"])
  \/ (\E r \in RMs : state[r] = "prepared" /\ state' = [state EXCEPT ![r] = "committed"])
  \/ (\E r \in RMs : state[r] = "prepared" /\ state' = [state EXCEPT ![r] = "aborted"])

Spec == Init /\ [][Next]_state

TypeOK ==
  state \in [RMs -> {"working", "prepared", "committed", "aborted"}]

ConsistencyInvariant ==
  \A r1, r2 \in RMs :
    \/ state[r1] = "working"
    \/ state[r2] = "working"
    \/ state[r1] = state[r2]
    \/ (state[r1] = "committed" /\ state[r2] = "aborted") = FALSE

THEOREM Spec => []TypeOK
THEOREM Spec => []ConsistencyInvariant
```
Note: This TLA+ specification does not explicitly include fairness conditions as they were not mentioned in the system description. If fairness conditions are required, additional variables and temporal logic formulas would need to be added to the specification.