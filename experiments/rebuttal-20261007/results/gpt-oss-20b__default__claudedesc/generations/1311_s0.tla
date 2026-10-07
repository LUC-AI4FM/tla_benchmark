MODULE EuclidSubtraction

EXTENDS Integers

VARIABLES u, v, pc

vars == <<u, v, pc>>

Init ==
  /\ u = 24
  /\ v \in 1..50
  /\ pc = "Lbl_1"

Lbl_1 ==
  /\ pc = "Lbl_1"
  /\ u' = u
  /\ v' = v
  /\ pc' = "Lbl_2"

Lbl_2 ==
  /\ pc = "Lbl_2"
  /\ u > 0
  /\ ( (u < v) /\ u' = v /\ v' = u )
     \/ ( (u >= v) /\ u' = u /\ v' = v )
  /\ pc' = "Lbl_3"

Lbl_3 ==
  /\ pc = "Lbl_3"
  /\ u > 0
  /\ ( (u - v > 0) /\ u' = u - v /\ v' = v /\ pc' = "Lbl_2" )
     \/ ( (u - v = 0) /\ u' = 0 /\ v' = v /\ pc' = "Done" )

Stutter ==
  /\ pc = "Done"
  /\ u' = u
  /\ v' = v
  /\ pc' = pc

Next == Lbl_1 \/ Lbl_2 \/ Lbl_3 \/ Stutter

Spec == Init /\ [][Next]_vars

===============================================================================