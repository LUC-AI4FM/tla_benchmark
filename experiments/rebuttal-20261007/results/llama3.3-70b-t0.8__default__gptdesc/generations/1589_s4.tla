```
MODULE Euclid
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
  /\ pc = "Start" =>
    /\ pc' = "Loop"
    /\ u' = u
    /\ v' = v
  /\ pc = "Loop" =>
    /\ IF v = 0
      THEN
        /\ pc' = "Done"
        /\ u' = u
        /\ v' = v
      ELSE
        /\ pc' = "Loop"
        /\ u' = v
        /\ v' = u MOD v
  /\ pc = "Done" => 
    /\ pc' = "Done"
    /\ u' = u
    /\ v' = v

Spec ==
  /\ Init
  /\ [][Next]_<<pc, u_ini, v_ini, u, v>>
  /\ WF_(<<pc, u_ini, v_ini, u, v>>, Next)

THEOREM Spec => []<>(pc = "Done" ∧ u = GCD(u_ini, v_ini))
GCD(a, b) == IF a = 0 THEN b ELSE GCD(b MOD a, a)
```