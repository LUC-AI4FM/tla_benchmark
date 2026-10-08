```
MODULE Euclid
EXTENDS Integers

CONSTANTS N

VARIABLES pc, u, v, v_ini

Init == 
  (pc = "Start") /\
  (u = 24) /\
  (v_ini \in 1..N) /\
  (v = v_ini)

Next == 
  IF pc = "Start" THEN
    ((pc = "Loop") /\ (v_ini = v))
  ELSE IF pc = "Loop" THEN
    IF u < v THEN
      ((pc = "Swap") /\ (u' = v) /\ (v' = u))
    ELSE IF u > v THEN
      ((pc = "Subtract") /\ (u' = u - v) /\ (v' = v))
    ELSE 
      ((pc = "Done"))
  ELSE IF pc = "Swap" THEN
    ((pc = "Loop") /\ (u' = u) /\ (v' = v))
  ELSE IF pc = "Subtract" THEN
    ((pc = "Loop") /\ (u' = u) /\ (v' = v))

Spec == Init /\ [][Next]_<<pc, u, v>>

Termination == <>(pc = "Done")

THEOREM Spec => []Termination
```