```tla
MODULE EuclidsAlgorithm

EXTENDS Integers, TLC

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
    /\ u_ini' = u_ini
    /\ v_ini' = v_ini
    /\ u' = u
    /\ v' = v
  ELSE IF pc = "Loop" THEN
    IF v = 0 THEN
      /\ pc' = "Done"
      /\ u_ini' = u_ini
      /\ v_ini' = v_ini
      /\ u' = u
      /\ v' = v
    ELSE
      /\ pc' = "Loop"
      /\ u_ini' = u_ini
      /\ v_ini' = v_ini
      /\ IF u < v THEN
          /\ u' = v
          /\ v' = u mod v
        ELSE
          /\ u' = u mod v
          /\ v' = v
  ELSE
    /\ pc' = pc
    /\ u_ini' = u_ini
    /\ v_ini' = v_ini
    /\ u' = u
    /\ v' = v

Spec ==
  /\ Init
  /\ [][Next]_<<pc, u_ini, v_ini, u, v>>
  /\ WF_<<pc, u_ini, v_ini, u, v>>(Next)

GCD(a, b) == IF b = 0 THEN a ELSE GCD(b, a mod b)

Correctness ==
  pc = "Done" => u = GCD(u_ini, v_ini)

THEOREM Spec => []Correctness

=============================================================================
```