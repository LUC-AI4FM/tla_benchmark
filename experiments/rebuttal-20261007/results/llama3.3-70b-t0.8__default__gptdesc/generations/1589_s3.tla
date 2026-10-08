```
MODULE EuclidAlgorithm
EXTENDS Integers

CONSTANTS MaxNum

VARIABLES pc, u_ini, v_ini, u, v

Init ==
  /\ pc = "Start"
  /\ u_ini \in 1..MaxNum
  /\ v_ini \in 1..MaxNum
  /\ u = u_ini
  /\ v = v_ini

Next ==
  IF pc = "Start" THEN
    /\ pc' = "Loop"
    /\ u' = u
    /\ v' = v
  ELSE IF pc = "Loop" THEN
    IF v = 0 THEN
      /\ pc' = "Done"
      /\ u' = u
      /\ v' = v
    ELSE
      /\ pc' = "Loop"
      /\ u' = v
      /\ v' = u % v
  ELSE
    /\ pc' = pc
    /\ u' = u
    /\ v' = v

Spec == Init /\ [][Next]_<<pc, u_ini, v_ini, u, v>>
Termination == <><pc = "Done">>
Fairness == WF_(Next)<<"Loop", "Start">>(pc)

GCDCorrectness == pc = "Done" => GCD(u_ini, v_ini) = u

THEOREM Spec => []GCDCorrectness
THEOREM Spec => Termination
```
Note: The `GCD` operator is not a built-in TLA+ operator. It should be defined separately using a mathematical definition of the greatest common divisor, such as:
```
GCD(m, n) == IF m = 0 THEN n ELSE GCD(n % m, m)
```