----------------------------- MODULE EuclidGCD -----------------------------

EXTENDS Naturals, Integers

CONSTANT N

ASSUME N \in Nat /\ N >= 1

VARIABLES pc, u, v, v_ini

vars == << pc, u, v, v_ini >>

RECURSIVE GCD(_, _)
GCD(m, n) == IF n = 0 THEN m ELSE GCD(n, m % n)

Init ==
  /\ pc = "lp"
  /\ u = 24
  /\ v \in 1..N
  /\ v_ini = v

LP_uZero ==
  /\ pc = "lp"
  /\ u = 0
  /\ pc' = "Done"
  /\ UNCHANGED << u, v, v_ini >>

LP_to_A_Swap ==
  /\ pc = "lp"
  /\ u # 0
  /\ u < v
  /\ pc' = "a"
  /\ u' = v
  /\ v' = u
  /\ UNCHANGED v_ini

LP_to_A_NoSwap ==
  /\ pc = "lp"
  /\ u # 0
  /\ u >= v
  /\ pc' = "a"
  /\ UNCHANGED << u, v, v_ini >>

A_to_LP ==
  /\ pc = "a"
  /\ u >= v
  /\ pc' = "lp"
  /\ u' = u - v
  /\ UNCHANGED << v, v_ini >>

Terminating ==
  /\ pc = "Done"
  /\ UNCHANGED vars

Next ==
  LP_uZero \/ LP_to_A_Swap \/ LP_to_A_NoSwap \/ A_to_LP \/ Terminating

Spec ==
  Init /\ [][Next]_vars /\ WF_vars(Next)

TypeOK ==
  /\ pc \in {"lp", "a", "Done"}
  /\ u \in Nat
  /\ v \in Nat
  /\ v_ini \in 1..N

AWellFormed ==
  (pc = "a") => u >= v

GCDInvariant ==
  GCD(u, v) = GCD(24, v_ini)

DoneCorrect ==
  (pc = "Done") => v = GCD(24, v_ini)

Termination ==
  <> (pc = "Done")

=============================================================================