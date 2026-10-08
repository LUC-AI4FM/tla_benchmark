------------------------------ MODULE EuclidSubtraction ------------------------------
EXTENDS Naturals

CONSTANT N

VARIABLES pc, u, v, v_ini

vars == <<pc,u,v,v_ini>>

Init ==
  /\ pc = "lp"
  /\ u = 24
  /\ v \in 1..N
  /\ v_ini = v

LpAction ==
  /\ pc = "lp"
  /\ u # 0
  /\ pc' = "a"
  /\ u' = IF u < v THEN v ELSE u
  /\ v' = IF u < v THEN u ELSE v
  /\ UNCHANGED <<v_ini>>

ZeroAction ==
  /\ pc = "lp"
  /\ u = 0
  /\ pc' = "Done"
  /\ UNCHANGED <<u,v,v_ini>>

AAction ==
  /\ pc = "a"
  /\ pc' = "lp"
  /\ u' = u - v
  /\ v' = v
  /\ UNCHANGED <<v_ini>>

Terminating ==
  /\ pc = "Done"
  /\ UNCHANGED vars

Next == LpAction \/ ZeroAction \/ AAction \/ Terminating

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

Termination == <> (pc = "Done")

RECURSIVE GCD
GCD == [x, y \in Nat |-> IF y = 0 THEN x ELSE GCD(y, Mod(x,y))]

=============================================================================