------------------------------ MODULE Euclid ------------------------------
EXTENDS Naturals

CONSTANTS N

VARIABLES u, v, v_ini, pc

vars == <<u,v,v_ini,pc>>

Init ==
  /\ u = 24
  /\ v \in 1..N
  /\ v_ini = v
  /\ pc = "Loop"

Next ==
  \/ /\ pc = "Loop" /\ u > v
     /\ u' = u - v
     /\ v' = v
     /\ pc' = "Loop"
     /\ v_ini' = v_ini
  \/ /\ pc = "Loop" /\ u < v
     /\ v' = v - u
     /\ u' = u
     /\ pc' = "Loop"
     /\ v_ini' = v_ini
  \/ /\ pc = "Loop" /\ u = v
     /\ pc' = "Done"
     /\ u' = u
     /\ v' = v
     /\ v_ini' = v_ini

Stutter ==
  \E vars' = vars

Spec == Init /\ [][Next \/ Stutter]_vars /\ WF_0(Next) /\ <> (pc = "Done")

=============================================================================