---- MODULE EuclidGCD ----
EXTENDS Naturals, Integers, TLC

VARIABLES a, b, b0, done

vars == << a, b, b0, done >>

Init ==
  /\ a = 24
  /\ b \in 1..50
  /\ b0 = b
  /\ done = FALSE

DoStep ==
  /\ ~done
  /\ a # 0
  /\ IF a < b
        THEN /\ a' = b
             /\ b' = a
             /\ done' = FALSE
        ELSE /\ a' = a - b
             /\ b' = b
             /\ done' = (a - b = 0)
  /\ UNCHANGED b0

Next ==
  DoStep \/ UNCHANGED vars

Spec ==
  Init /\ [][Next]_vars /\ WF_vars(DoStep)

GCD(m, n) ==
  IF n = 0 THEN m ELSE GCD(n, m % n)

Termination ==
  <>done
====