---------------------------- MODULE ABSpec ----------------------------
EXTENDS Naturals

CONSTANT Data

ConstData == {"d1", "d2"}

VARIABLES AVar, BVar

vars == <<AVar, BVar>>

Bits == {0, 1}

Messages == Data \X Bits

ABSpec_TypeOK == /\ AVar \in Messages
                 /\ BVar \in Messages

Init == /\ AVar \in Data \X {1}
        /\ BVar = AVar

A == /\ AVar = BVar
     /\ \E d \in Data : AVar' = <<d, 1 - AVar[2]>>
     /\ BVar' = BVar

B == /\ AVar # BVar
     /\ BVar' = AVar
     /\ AVar' = AVar

Next == A \/ B

Spec == Init /\ [][Next]_vars

FairSpec == Spec /\ WF_vars(Next)

ABSpec_Inv == (AVar[2] = BVar[2]) => (AVar = BVar)

DataSafety == /\ AVar[1] \in Data
              /\ BVar[1] \in Data

Progress == \A v \in Messages : (AVar = v) ~> (BVar = v)

THEOREM Spec => [](ABSpec_TypeOK /\ ABSpec_Inv /\ DataSafety)
=============================================================================