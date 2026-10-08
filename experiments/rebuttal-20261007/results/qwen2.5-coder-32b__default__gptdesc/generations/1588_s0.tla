------------------------------- MODULE EuclidAlgorithm -------------------------------
EXTENDS Naturals, TLC

CONSTANTS N

VARIABLES u, v, v_ini, pc

Init == /\ u = 24
        /\ v \in 1..N
        /\ v_ini = v
        /\ pc = "start"

Next ==
    \/ /\ pc = "start"
       /\ u >= v
       /\ u' = u - v
       /\ v' = v
       /\ v_ini' = v_ini
       /\ pc' = "loop"
    \/ /\ pc = "start"
       /\ u < v
       /\ u' = u
       /\ v' = v
       /\ v_ini' = v_ini
       /\ pc' = "swap"
    \/ /\ pc = "loop"
       /\ u >= v
       /\ u' = u - v
       /\ v' = v
       /\ v_ini' = v_ini
       /\ pc' = "loop"
    \/ /\ pc = "loop"
       /\ u < v
       /\ u' = u
       /\ v' = v
       /\ v_ini' = v_ini
       /\ pc' = "swap"
    \/ /\ pc = "swap"
       /\ u' = v
       /\ v' = u
       /\ v_ini' = v_ini
       /\ pc' = "loop"
    \/ /\ pc = "loop"
       /\ u = v
       /\ u' = u
       /\ v' = v
       /\ v_ini' = v_ini
       /\ pc' = "Done"

Spec ==
    /\ Init
    /\ [][Next]_<<u, v, v_ini, pc>>
    /\ WF_[Next]_<<u, v, v_ini, pc>>

Termination == <>[](pc = "Done")

=============================================================================