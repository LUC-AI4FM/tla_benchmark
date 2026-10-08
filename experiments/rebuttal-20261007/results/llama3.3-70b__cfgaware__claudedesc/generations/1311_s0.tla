---------------------------- MODULE Euclid --------------------------------
EXTENDS Integers

CONSTANTS None

VARIABLES u, v, pc

Init == (u = 24) /\ (v \in 1..50) /\ (pc = "Lbl_1")

Lbl_1 == (pc = "Lbl_1") /\ (pc' = "Lbl_2")

Lbl_2 == (pc = "Lbl_2") /\ 
         IF u < v
         THEN (u, v) := (v, u)
         ELSE TRUE
         /\ (pc' = "Lbl_3")

Lbl_3 == (pc = "Lbl_3") /\ (u > 0) /\ (u' = u - v) /\ (v' = v) /\ (pc' = "Lbl_2")

Done == (pc = "Done") /\ (u' = u) /\ (v' = v) /\ (pc' = "Done")

Next == Lbl_1 \/ Lbl_2 \/ Lbl_3 \/ ((pc = "Done") /\ Done)

Spec == Init /\ [][Next]_(u, v, pc)
=============================================================================