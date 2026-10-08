```
MODULE GCD
EXTENDS Integers

CONSTANTS

VARIABLES u, v, pc

Init ==
  (u = 24) /\
  (v \in 1..50) /\
  (pc = "Start")

Start == 
  (pc = "Start") /\
  (pc' = "Loop") /\
  (u' = u) /\
  (v' = v)

Swap ==
  (pc = "Loop") /\
  (u < v) /\
  (pc' = "Loop") /\
  (u' = v) /\
  (v' = u)

Subtract ==
  (pc = "Loop") /\
  (~ (u < v)) /\
  (pc' = "Loop") /\
  (u' = u - v) /\
  (v' = v)

Done == 
  (pc = "Loop") /\
  (u = 0) /\
  (pc' = "Done") /\
  (u' = u) /\
  (v' = v)

Stutter ==
  (pc = "Done") /\
  (pc' = "Done") /\
  (u' = u) /\
  (v' = v)

Next == 
  Start \/ Swap \/ Subtract \/ Done \/ Stutter

Spec == Init /\ [][Next]_<<u, v, pc>>
```