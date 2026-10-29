---------------------------- MODULE MCSession11a ----------------------------
EXTENDS Integers

CONSTANT Data

VARIABLES AVar, BVar

vars == <<AVar, BVar>>

MCData == {"d1", "d2", "d3"}

Msgs == [val : Data, bit : {0, 1}]

Init ==
    /\ AVar \in Msgs
    /\ BVar = AVar

A ==
    /\ AVar.bit = BVar.bit
    /\ \E d \in Data :
          AVar' = [val |-> d, bit |-> 1 - AVar.bit]
    /\ UNCHANGED BVar

B ==
    /\ AVar.bit # BVar.bit
    /\ BVar' = AVar
    /\ UNCHANGED AVar

Next == A \/ B

Spec == Init /\ [][Next]_vars

TypeOK ==
    /\ AVar \in Msgs
    /\ BVar \in Msgs

Inv == (AVar.bit = BVar.bit) => (AVar = BVar)

THEOREM Spec => [](TypeOK /\ Inv)
=============================================================================