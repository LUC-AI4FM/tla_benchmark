```
MODULE GCD
EXTENDS Integers

CONSTANTS 

VARIABLES u, v, pc

Init ==
  /\ u = 24
  /\ v \in 1..50
  /\ pc = "Start"

Start == 
  /\ pc = "Start"
  /\ pc' = "Loop"
  /\ u' = u
  /\ v' = v

Loop == 
  /\ pc = "Loop"
  /\ IF u < v THEN
      /\ pc' = "Swap"
      /\ u' = v
      /\ v' = u
    ELSE
      /\ pc' = "Subtract"
      /\ u' = u - v
      /\ v' = v

Swap == 
  /\ pc = "Swap"
  /\ pc' = "Loop"
  /\ u' = u
  /\ v' = v

Subtract == 
  /\ pc = "Subtract"
  /\ IF u = 0 THEN
      /\ pc' = "Done"
      /\ u' = u
      /\ v' = v
    ELSE
      /\ pc' = "Loop"
      /\ u' = u - v
      /\ v' = v

Done == 
  /\ pc = "Done"
  /\ pc' = "Done"
  /\ u' = u
  /\ v' = v

Next ==
  \/ Start
  \/ Loop
  \/ Swap
  \/ Subtract
  \/ Done

Spec == Init /\ [][Next]_<<u, v, pc>>
```