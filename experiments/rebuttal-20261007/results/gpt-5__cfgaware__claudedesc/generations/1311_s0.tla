------------------------------ MODULE EuclidGCD ------------------------------

EXTENDS Integers

VARIABLES u, v, pc

vars == << u, v, pc >>

Init ==
  /\ u = 24
  /\ v \in 1..50
  /\ pc = "Lbl_1"

Lbl_1 ==
  /\ pc = "Lbl_1"
  /\ pc' = "Lbl_2"
  /\ UNCHANGED << u, v >>

Lbl_2 ==
  /\ pc = "Lbl_2"
  /\ IF u = 0
        THEN /\ pc' = "Done"
             /\ UNCHANGED << u, v >>
        ELSE /\ pc' = "Lbl_3"
             /\ IF u < v
                   THEN /\ u' = v
                        /\ v' = u
                   ELSE /\ UNCHANGED << u, v >>

Lbl_3 ==
  /\ pc = "Lbl_3"
  /\ u' = u - v
  /\ pc' = "Lbl_2"
  /\ UNCHANGED v

Next ==
  Lbl_1 \/ Lbl_2 \/ Lbl_3
  \/ (/\ pc = "Done"
      /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

=============================================================================