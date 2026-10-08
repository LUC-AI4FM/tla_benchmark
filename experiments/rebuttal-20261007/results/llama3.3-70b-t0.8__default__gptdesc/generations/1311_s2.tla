```
MODULE GCD
EXTENDS Integers

CONSTANTS 
  MaxV

VARIABLES 
  u, v, pc

Init ==
  /\ u = 24
  /\ v \in 1..MaxV
  /\ pc = "Start"

Next ==
  \/ (pc = "Start" /\ u' = u /\ v' = v /\ pc' = "Swap")
  \/ (pc = "Swap" /\ u < v /\ u' = v /\ v' = u /\ pc' = "Subtract")
  \/ (pc = "Swap" /\ u >= v /\ u' = u /\ v' = v /\ pc' = "Subtract")
  \/ (pc = "Subtract" /\ u >= v /\ u' = u - v /\ v' = v /\ pc' = "Swap")
  \/ (pc = "Subtract" /\ u < v /\ u' = u /\ v' = v /\ pc' = "Done")
  \/ (pc = "Done" /\ u' = u /\ v' = v /\ pc' = pc)

Spec == 
  /\ Init
  /\ [][Next]_<<u, v, pc>>
```