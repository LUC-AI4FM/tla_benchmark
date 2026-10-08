```
MODULE GCD
EXTENDS Integers

CONSTANTS

VARIABLES u, v, pc

Init ==
  /\ u = 24
  /\ v \in 1..50
  /\ pc = "Start"

Next ==
  /\ (pc = "Start") => 
    /\ pc' = "Swap"
    /\ u' = u
    /\ v' = v
  \/ (pc = "Swap") =>
    /\ (u < v) => 
      /\ pc' = "Swap"
      /\ u' = v
      /\ v' = u
    \/ (u >= v) => 
      /\ pc' = "Subtract"
      /\ u' = u
      /\ v' = v
  \/ (pc = "Subtract") =>
    /\ (u > 0) => 
      /\ pc' = "Swap"
      /\ u' = u - v
      /\ v' = v
    \/ (u = 0) => 
      /\ pc' = "Done"
      /\ u' = u
      /\ v' = v
  \/ (pc = "Done") =>
    /\ pc' = pc
    /\ u' = u
    /\ v' = v

Spec == Init /\ [][Next]_<<u, v, pc>>
```