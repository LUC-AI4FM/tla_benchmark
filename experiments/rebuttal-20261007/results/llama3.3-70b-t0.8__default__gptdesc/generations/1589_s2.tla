```
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
  /\ pc = "Start" =>
    /\ pc' = "Loop"
    /\ u_ini' = u_ini
    /\ v_ini' = v_ini
    /\ u' = u
    /\ v' = v
  /\ pc = "Loop" =>
    /\ IF v = 0
      THEN
        /\ pc' = "Done"
        /\ u_ini' = u_ini
        /\ v_ini' = v_ini
        /\ u' = u
        /\ v' = v
      ELSE
        /\ IF u < v
          THEN
            /\ pc' = "Swap"
            /\ u_ini' = u_ini
            /\ v_ini' = v_ini
            /\ u' = v
            /\ v' = u
          ELSE
            /\ pc' = "Loop"
            /\ u_ini' = u_ini
            /\ v_ini' = v_ini
            /\ u' = u - (u \div v) * v
            /\ v' = v
  /\ pc = "Swap" =>
    /\ pc' = "Loop"
    /\ u_ini' = u_ini
    /\ v_ini' = v_ini
    /\ u' = v
    /\ v' = u
  /\ pc = "Done" =>
    /\ UNCHANGED <<pc, u_ini, v_ini, u, v>>

Spec ==
  /\ Init
  /\ [][Next]_<<pc, u_ini, v_ini, u, v>>
  /\ WF_vars(Next, <<pc, u_ini, v_ini, u, v>>)

Correctness ==
  pc = "Done" => GCD(u_ini, v_ini) = u

GCD(a, b) == 
  IF a = 0 THEN b
  ELSE IF b = 0 THEN a
  ELSE GCD(b, a % b)
```