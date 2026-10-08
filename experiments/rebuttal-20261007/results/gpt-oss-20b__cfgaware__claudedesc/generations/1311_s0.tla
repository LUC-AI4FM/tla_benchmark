------------------------------ MODULE EuclidSubtraction ------------------------------
VARIABLES u, v, pc

vars == <<u, v, pc>>

Init ==
    /\ u = 24
    /\ v \in 1..50
    /\ pc = "Lbl_1"

Lbl_1 ==
    /\ pc = "Lbl_1"
    /\ pc' = "Lbl_2"
    /\ UNCHANGED <<u, v>>

Lbl_2 ==
    /\ pc = "Lbl_2"
    /\ ( u = 0
         /\ pc' = "Done"
         /\ UNCHANGED <<u, v>> )
       \/ ( u # 0
            /\ u < v
            /\ u' = v
            /\ v' = u
            /\ pc' = "Lbl_3" )
       \/ ( u # 0
            /\ u >= v
            /\ UNCHANGED <<u, v>>
            /\ pc' = "Lbl_3")

Lbl_3 ==
    /\ pc = "Lbl_3"
    /\ u' = u - v
    /\ UNCHANGED <<v>>
    /\ pc' = "Lbl_2"

Stutter ==
    /\ pc = "Done"
    /\ pc' = pc
    /\ UNCHANGED <<u, v>>

Next == Lbl_1 \/ Lbl_2 \/ Lbl_3 \/ Stutter

Spec == Init /\ [][Next]_(vars)

=============================================================================