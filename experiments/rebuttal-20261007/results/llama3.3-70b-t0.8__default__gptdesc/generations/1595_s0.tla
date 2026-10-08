```
MODULE Counter
EXTENDS Integers

CONSTANTS

VARIABLES pc, x

Init ==
  (pc = "Start") /\
  (x = 0)

Next ==
  (pc = "Start") /\ (x < 10) /\ (pc' = "Loop") /\ (x' = x + 1) \*
  (pc = "Loop") /\ (x < 10) /\ (pc' = "Loop") /\ (x' = x + 1) \*
  (pc = "Loop") /\ (x = 10) /\ (pc' = "Done") /\ (x' = x) \*
  (pc = "Done") /\ (UNCHANGED <<pc, x>>)

Spec == Init /\ [][Next]_<<pc, x>>
Termination == <>(pc = "Done")
Fairness == WF_<<pc, x>>(Next)
AtFive == (x = 5)
FinishLoop == (pc = "Loop") /\ (x >= 10)
PossibleCounts == (x \in 0..11)

THEOREM Spec => []Termination
```
Note: The code has been formatted according to standard TLA+ coding conventions. However, the ` PossibleCounts` definition may require additional TLC configuration for verification as it is related to model checking specific state counts rather than being a direct part of the system's temporal logic specification.