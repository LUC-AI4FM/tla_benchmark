------------------------------- MODULE EuclidGCD -------------------------------
EXTENDS Integers

CONSTANTS v_init \* v is chosen nondeterministically from 1 to 50

VARIABLES u, v, pc

Init == /\ u = 24
        /\ v \in 1..50
        /\ pc = "Lbl_1"

Next ==
    \/ /\ pc = "Lbl_1"
       /\ UNCHANGED <<u, v>>
       /\ pc' = "Lbl_2"
    \/ /\ pc = "Lbl_2"
       /\ u # 0
       /\ (\/ /\ u >= v
              /\ u' = u - v
              /\ v' = v
           \/ /\ u < v
              /\ u' = v
              /\ v' = u)
       /\ pc' = "Lbl_3"
    \/ /\ pc = "Lbl_2"
       /\ u = 0
       /\ UNCHANGED <<u, v>>
       /\ pc' = "Done"
    \/ /\ pc = "Lbl_3"
       /\ UNCHANGED <<u, v>>
       /\ pc' = "Lbl_2"
    \/ /\ pc \in {"Lbl_1", "Lbl_2", "Lbl_3", "Done"}
       /\ UNCHANGED <<u, v, pc>>

Spec == Init /\ [][Next]_<<u, v, pc>>
=============================================================================