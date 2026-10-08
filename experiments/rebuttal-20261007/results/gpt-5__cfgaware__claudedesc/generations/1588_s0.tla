----------------------------- MODULE EuclidSubGCD -----------------------------
EXTENDS Naturals, Integers

CONSTANT N

VARIABLES pc, u, v, v_ini

vars == << pc, u, v, v_ini >>

Init ==
  /\ pc = "lp"
  /\ u = 24
  /\ v \in 1..N
  /\ v_ini = v

LpToA ==
  /\ pc = "lp"
  /\ u # 0
  /\ IF u < v
        THEN /\ u' = v
             /\ v' = u
        ELSE /\ u' = u
             /\ v' = v
  /\ pc' = "a"
  /\ UNCHANGED v_ini

LpDone ==
  /\ pc = "lp"
  /\ u = 0
  /\ pc' = "Done"
  /\ UNCHANGED <<u, v, v_ini>>

Astep ==
  /\ pc = "a"
  /\ u' = u - v
  /\ UNCHANGED <<v, v_ini>>
  /\ pc' = "lp"

Terminating ==
  /\ pc = "Done"
  /\ UNCHANGED vars

Next == LpDone \/ LpToA \/ Astep \/ Terminating

RECURSIVE GCD(_, _)
GCD(m, n) == IF n = 0 THEN m ELSE GCD(n, m % n)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

Termination == <> (pc = "Done")
=============================================================================