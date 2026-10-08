------------------------------- MODULE EuclidsAlgorithm ------------------------------
EXTENDS Naturals, TLC

CONSTANTS N

VARIABLES u, v, v_ini, pc

Init == /\ u = 24 
        /\ v \in (1..N)
        /\ v_ini = v
        /\ pc = "Start"

Next ==
    \/ /\ pc = "Start"
       /\ u >= v
       /\ u' = u - v
       /\ v' = v
       /\ v_ini' = v_ini
       /\ pc' = "Loop"
     \/ /\ pc = "Start"
        /\ u < v
        /\ u' = u
        /\ v' = v
        /\ v_ini' = v_ini
        /\ pc' = "Swap"
     \/ /\ pc = "Loop"
        /\ u >= v
        /\ u' = u - v
        /\ v' = v
        /\ v_ini' = v_ini
        /\ pc' = "Loop"
     \/ /\ pc = "Loop"
        /\ u < v
        /\ u' = u
        /\ v' = v
        /\ v_ini' = v_ini
        /\ pc' = "Swap"
     \/ /\ pc = "Swap"
        /\ u' = v
        /\ v' = u
        /\ v_ini' = v_ini
        /\ pc' = "Loop"
     \/ /\ pc = "Loop"
        /\ u = v
        /\ u' = u
        /\ v' = v
        /\ v_ini' = v_ini
        /\ pc' = "Done"

Spec == Init /\ [][Next]_<<u, v, v_ini, pc>> /\ WF_[Next]_<<u, v, v_ini, pc>>

\* Termination property
Terminated == pc = "Done"
=============================================================================