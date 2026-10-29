------------------------------- MODULE ABSpec -------------------------------
EXTENDS Integers

CONSTANT Data

VARIABLES AVar, BVar

vars == << AVar, BVar >>

Msg == [data : Data, bit : {0, 1}]

TypeOK == /\ AVar \in Msg
          /\ BVar \in Msg

Init == /\ AVar \in [data : Data, bit : {1}]
        /\ BVar = AVar

A == /\ AVar = BVar
     /\ \E d \in Data : AVar' = [data |-> d, bit |-> 1 - AVar.bit]
     /\ BVar' = BVar

B == /\ AVar # BVar
     /\ BVar' = AVar
     /\ AVar' = AVar

Next == A \/ B

Spec == Init /\ [][Next]_vars

THEOREM Spec => []TypeOK
=============================================================================