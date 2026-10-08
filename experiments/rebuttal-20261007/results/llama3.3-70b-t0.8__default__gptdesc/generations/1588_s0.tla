```
MODULE EuclidsAlgorithm
EXTENDS Integers

CONSTANTS N

VARIABLES pc, u, v, v_ini

Init ==
  /\ pc = "Start"
  /\ u = 24
  /\ v_ini \in 1..N
  /\ v = v_ini

Next ==
  \/ pc = "Start" /\ pc' = "Swap" /\ u' = u /\ v' = v
  \/ pc = "Swap" /\ v > u /\ pc' = "Subtract" /\ u' = u /\ v' = v - u
  \/ pc = "Swap" /\ v <= u /\ pc' = "Done" /\ u' = u /\ v' = v
  \/ pc = "Subtract" /\ u >= v /\ pc' = "Swap" /\ u' = v /\ v' = u
  \/ pc = "Subtract" /\ u < v /\ pc' = "Subtract" /\ u' = u /\ v' = v - u
  \/ pc' = pc /\ u' = u /\ v' = v

Spec ==
  Init /\ [][Next]_<<pc, u, v>>

Termination ==
  <> (pc = "Done")

THEOREM Spec => []Termination
```