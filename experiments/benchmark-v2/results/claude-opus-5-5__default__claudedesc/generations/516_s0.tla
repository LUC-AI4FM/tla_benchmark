---------------------------- MODULE ABSpec ----------------------------
EXTENDS Integers

CONSTANT Data

VARIABLES AVar, BVar

vars == <<AVar, BVar>>

Msg == [data : Data, bit : {0, 1}]

TypeOK == /\ AVar \in Msg
          /\ BVar \in Msg

Init == /\ AVar \in [data : Data, bit : {1}]
        /\ BVar = AVar

A == /\ AVar.bit = BVar.bit
     /\ \E d \in Data :
          AVar' = [data |-> d, bit |-> 1 - AVar.bit]
     /\ UNCHANGED BVar

B == /\ AVar.bit # BVar.bit
     /\ BVar' = AVar
     /\ UNCHANGED AVar

Next == A \/ B

Spec == Init /\ [][Next]_vars /\ WF_vars(A) /\ WF_vars(B)

-----------------------------------------------------------------------------
THEOREM Spec => []TypeOK
=============================================================================