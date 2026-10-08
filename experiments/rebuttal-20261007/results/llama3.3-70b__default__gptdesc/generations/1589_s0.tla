```
MODULE EuclidsAlgorithm
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
      /\ v' = u MOD v
  ELSE
    /\ pc' = pc
    /\ u' = u
    /\ v' = v

Spec == Init /\ [][Next]_<<pc, u_ini, v_ini, u, v>>
Termination == <><pc = "Done">_
Fairness == WF_(Next)_(pc)

Correctness == []<>(pc = "Done" => u = GCD(u_ini, v_ini))

THEOREM Spec => []Correctness
THEOREM Spec => Termination

GCD(a, b) == IF a = 0 THEN b ELSE GCD(b MOD a, a)
```