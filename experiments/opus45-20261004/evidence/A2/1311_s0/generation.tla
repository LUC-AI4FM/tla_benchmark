---------------------------- MODULE EuclidGCD ----------------------------
EXTENDS Integers, TLC

CONSTANTS PrintVal

VARIABLES u, v, pc

vars == <<u, v, pc>>

Init ==
    /\ u = 24
    /\ v \in 1..50
    /\ pc = "Lbl_1"

Lbl_1 ==
    /\ pc = "Lbl_1"
    /\ PrintVal(<<u, v>>)
    /\ pc' = "Lbl_2"
    /\ UNCHANGED <<u, v>>

Lbl_2 ==
    /\ pc = "Lbl_2"
    /\ IF u /= 0
       THEN /\ IF u < v
               THEN /\ u' = v
                    /\ v' = u
               ELSE /\ TRUE
                    /\ UNCHANGED <<u, v>>
            /\ pc' = "Lbl_3"
       ELSE /\ pc' = "Done"
            /\ UNCHANGED <<u, v>>

Lbl_3 ==
    /\ pc = "Lbl_3"
    /\ u' = u - v
    /\ pc' = "Lbl_2"
    /\ UNCHANGED v

Terminating ==
    /\ pc = "Done"
    /\ UNCHANGED vars

Next ==
    \/ Lbl_1
    \/ Lbl_2
    \/ Lbl_3
    \/ Terminating

Spec == Init /\ [][Next]_vars

==========================================================================