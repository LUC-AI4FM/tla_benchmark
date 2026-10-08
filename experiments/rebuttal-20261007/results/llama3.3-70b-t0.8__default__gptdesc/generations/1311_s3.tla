```
MODULE GCD
EXTENDS Integers

CONSTANTS 

VARIABLES u, v, pc

Init ==
  (u = 24) /\ (v \in 1..50) /\ (pc = "Start")

Start == 
  (pc = "Start") /\ (u' = u) /\ (v' = v) /\ (pc' = "Loop")

Swap == 
  (pc = "Loop") /\ (u < v) /\ (u' = v) /\ (v' = u) /\ (pc' = "Loop")

Subtract == 
  (pc = "Loop") /\ ~(u < v) /\ (u' = u - v) /\ (v' = v) /\ (pc' = "Loop")

Done == 
  (pc = "Loop") /\ (u = 0) /\ (u' = u) /\ (v' = v) /\ (pc' = "Done")

Next ==
  \/ Start
  \/ Swap
  \/ Subtract
  \/ Done
  \/ (pc = "Done") /\ (u' = u) /\ (v' = v) /\ (pc' = pc)

Spec == 
  Init /\ [][Next]_(u, v, pc)
```