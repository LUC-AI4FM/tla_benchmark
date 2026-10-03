```
MODULE GCD
VARIABLES u, v, pc

Init ==
  /\ u = 24
  /\ v \in 1..50
  /\ pc = "Start"

Next ==
  \/ pc = "Start" /\ pc' = "Loop" /\ u' = u /\ v' = v
  \/ pc = "Loop" /\ u < v /\ pc' = "Swap" /\ u' = v /\ v' = u
  \/ pc = "Loop" /\ ~(u < v) /\ pc' = "Subtract" /\ u' = u - v /\ v' = v
  \/ pc = "Swap" /\ pc' = "Loop" /\ u' = u /\ v' = v
  \/ pc = "Subtract" /\ u > 0 /\ pc' = "Loop" /\ u' = u /\ v' = v
  \/ pc = "Subtract" /\ u = 0 /\ pc' = "Done" /\ u' = u /\ v' = v
  \/ pc = "Done" /\ pc' = "Done" /\ u' = u /\ v' = v

Spec == Init /\ [][Next]_<<u, v, pc>>
```
Note: The `<<u, v, pc>>` in the `Spec` definition is used to specify the variables that can change over time. This is necessary for the model checker to know which variables to consider when checking the temporal formula.