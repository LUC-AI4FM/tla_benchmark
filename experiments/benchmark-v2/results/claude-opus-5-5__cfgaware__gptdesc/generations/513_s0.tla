---------------------------- MODULE MCSession11a ----------------------------
EXTENDS Integers, TLC

CONSTANT Data

VARIABLES AVar, BVar

vars == <<AVar, BVar>>

ConstData == {"d1", "d2"}

Msgs == [data : Data, bit : {0, 1}]

Init ==
    /\ AVar \in [data : Data, bit : {1}]
    /\ BVar = AVar

A ==
    /\ AVar = BVar
    /\ \E d \in Data :
         AVar' = [data |-> d, bit |-> 1 - AVar.bit]
    /\ UNCHANGED BVar

B ==
    /\ AVar /= BVar
    /\ BVar' = AVar
    /\ UNCHANGED AVar

Next == A \/ B

Spec == Init /\ [][Next]_vars

ABSpec_TypeOK ==
    /\ AVar \in Msgs
    /\ BVar \in Msgs

ABSpec_Inv ==
    (AVar.bit = BVar.bit) => (AVar = BVar)

=============================================================================