```
MODULE EuclidGCD
EXTENDS Integers

CONSTANTS 

VARIABLES u, v, pc

Init == (u = 24) /\ (v \in 1..50) /\ (pc = "Lbl_1")

Lbl_1 == (pc = "Lbl_1") /\ (pc' = "Lbl_2")

Lbl_2 == (pc = "Lbl_2") /\ 
         IF u < v
         THEN (u, v)' = (v, u)
         ELSE (u, v)' = (u, v) /\ 
         (pc' = IF u = 0 THEN "Done" ELSE "Lbl_3")

Lbl_3 == (pc = "Lbl_3") /\ (u' = u - v) /\ (v' = v) /\ (pc' = "Lbl_2")

Next == Lbl_1 \/ Lbl_2 \/ Lbl_3 \/ (pc = "Done" /\ (u, v, pc)' = (u, v, pc))

Spec == Init /\ [][Next]_(u, v, pc)
```