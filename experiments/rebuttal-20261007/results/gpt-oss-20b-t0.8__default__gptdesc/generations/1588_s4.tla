----------------------------- MODULE Euclid -----------------------------
EXTENDS Naturals, Sequences

CONSTANT N

VARIABLES u, v, v_ini, pc

Init == /\ pc = "Init"
        /\ u = 24
        /\ v \in 1..N
        /\ v_ini = v

Next ==
  \/ /\ pc = "Init"
     /\ pc' = "Loop"
     /\ UNCHANGED <<u, v, v_ini>>
  \/ /\ pc = "Loop" /\ u # v /\ u > v
     /\ u' = u - v
     /\ v' = v
     /\ pc' = "Loop"
  \/ /\ pc = "Loop" /\ u # v /\ u <= v
     /\ u' = u
     /\ v' = v - u
     /\ pc' = "Loop"
  \/ /\ pc = "Loop" /\ u = v
     /\ pc' = "Done"
     /\ UNCHANGED <<u, v, v_ini>>
  \/ /\ UNCHANGED <<u, v, v_ini, pc>>

Spec == Init /\ [][Next]_<<u, v, v_ini, pc>> /\ WF_vars(Next)

TerminationProp == <> (pc = "Done")
===============================================================================