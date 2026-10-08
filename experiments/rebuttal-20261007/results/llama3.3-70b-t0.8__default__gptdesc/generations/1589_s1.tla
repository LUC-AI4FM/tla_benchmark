```
MODULE EuclidsAlgorithm
EXTENDS Integers

CONSTANTS MaxNum

VARIABLES pc, u_ini, v_ini, u, v

Init == 
  (pc = "Start") /\ 
  (u_ini \in 1..MaxNum) /\ 
  (v_ini \in 1..MaxNum) /\ 
  (u = u_ini) /\ 
  (v = v_ini)

Next == 
  IF pc = "Start" THEN
    (pc' = "Loop") /\ 
    (u_ini' = u_ini) /\ 
    (v_ini' = v_ini) /\ 
    (u' = u) /\ 
    (v' = v)
  ELSE IF pc = "Loop" THEN
    IF u = 0 THEN
      (pc' = "Done") /\ 
      (u_ini' = u_ini) /\ 
      (v_ini' = v_ini) /\ 
      (u' = u) /\ 
      (v' = v)
    ELSE IF v = 0 THEN
      (pc' = "Done") /\ 
      (u_ini' = u_ini) /\ 
      (v_ini' = v_ini) /\ 
      (u' = u) /\ 
      (v' = v)
    ELSE IF u > v THEN
      (pc' = "Loop") /\ 
      (u_ini' = u_ini) /\ 
      (v_ini' = v_ini) /\ 
      (u' = u - v) /\ 
      (v' = v)
    ELSE
      (pc' = "Loop") /\ 
      (u_ini' = u_ini) /\ 
      (v_ini' = v_ini) /\ 
      (u' = u) /\ 
      (v' = v - u)
  ELSE
    (pc' = pc) /\ 
    (u_ini' = u_ini) /\ 
    (v_ini' = v_ini) /\ 
    (u' = u) /\ 
    (v' = v)

Spec == Init /\ [][Next]_<<pc, u_ini, v_ini, u, v>>
WeakFairness == WF pc ("Start" | "Loop")

GCDCorrect == 
  pc = "Done" => v = GCD(u_ini, v_ini)

THEOREM Spec => []GCDCorrect

Termination == <>(pc = "Done")
```
Note: This TLA+ specification does not include the definition of the `GCD` operator. You may need to add it depending on your specific requirements. 

In a typical case, you could define GCD as follows:

```
GCD(a, b) == 
  IF a = 0 THEN b
  ELSE IF b = 0 THEN a
  ELSE IF a > b THEN GCD(a - b, b)
  ELSE GCD(a, b - a)
```