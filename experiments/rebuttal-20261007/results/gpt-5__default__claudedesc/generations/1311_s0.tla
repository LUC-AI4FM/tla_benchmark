------------------------------ MODULE EuclidGCD ------------------------------

EXTENDS Naturals, Integers

CONSTANTS UInit, VMax
ASSUME UInit = 24 /\ VMax = 50

VARIABLES u, v, pc

vars == <<u, v, pc>>

Init ==
  /\ u = UInit
  /\ v \in 1..VMax
  /\ pc = "Lbl_1"

Lbl_1 ==
  /\ pc = "Lbl_1"
  /\ pc' = "Lbl_2"
  /\ UNCHANGED <<u, v>>

Lbl_2 ==
  /\ pc = "Lbl_2"
  /\ IF u = 0 THEN
        /\ pc' = "Done"
        /\ UNCHANGED <<u, v>>
     ELSE
        /\ IF u < v THEN
              /\ u' = v
              /\ v' = u
           ELSE
              /\ u' = u
              /\ v' = v
        /\ pc' = "Lbl_3"

Lbl_3 ==
  /\ pc = "Lbl_3"
  /\ u' = u - v
  /\ pc' = "Lbl_2"
  /\ UNCHANGED v

Term ==
  /\ pc = "Done"
  /\ UNCHANGED vars

Next ==
  Lbl_1 \/ Lbl_2 \/ Lbl_3 \/ Term

Spec ==
  Init /\ [][Next]_vars

==========================================