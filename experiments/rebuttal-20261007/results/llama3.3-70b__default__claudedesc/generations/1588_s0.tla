```
MODULE EuclidSubtractionAlgorithm
EXTENDS Integers

CONSTANTS N

VARIABLES pc, u, v, v_ini

Init == 
  (pc = "lp") /\ 
  (u = 24) /\ 
  (v \in 1..N) /\ 
  (v_ini = v)

GCD(a, b) == 
  IF a = 0 THEN b
  ELSE GCD(b % a, a)

Next == 
  ((pc = "lp") /\ (u # 0) /\ (u < v)) /\ (pc' = "a") /\ (u' = v) /\ (v' = u) /\ (v_ini' = v_ini)
  \/
  ((pc = "lp") /\ (u # 0) /\ (u >= v)) /\ (pc' = "a") /\ (u' = u) /\ (v' = v) /\ (v_ini' = v_ini)
  \/
  ((pc = "a") /\ (u > v)) /\ (pc' = "lp") /\ (u' = u - v) /\ (v' = v) /\ (v_ini' = v_ini)
  \/
  ((pc = "a") /\ (u <= v)) /\ (pc' = "lp") /\ (u' = u) /\ (v' = v) /\ (v_ini' = v_ini)
  \/
  ((pc = "lp") /\ (u = 0)) /\ (pc' = "Done") /\ (u' = u) /\ (v' = v) /\ (v_ini' = v_ini)
  \/
  ((pc = "Done") /\ (u' = u) /\ (v' = v) /\ (v_ini' = v_ini) /\ (pc' = "Done"))

Terminating == 
  (pc = "Done") /\ (u' = u) /\ (v' = v) /\ (v_ini' = v_ini) /\ (pc' = "Done")

Spec == 
  Init /\ [][Next]_<<pc, u, v, v_ini>> /\ WF_<<pc, u, v, v_ini>>(Terminating)

Termination == 
  <>[](pc = "Done")
```