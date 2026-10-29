---------------------------- MODULE ABSpec ----------------------------
EXTENDS Naturals

CONSTANT Data

VARIABLES AVar, BVar

vars == <<AVar, BVar>>

ConstData == {"Ann", "Bob", "Cal"}

TypeOK == /\ AVar \in Data \X {0, 1}
          /\ BVar \in Data \X {0, 1}

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

Inv == (AVar[2] = BVar[2]) => (AVar = BVar)

ABSpec_TypeOK == TypeOK

ABSpec_Inv == Inv

FairSpec == Spec /\ WF_vars(Next)

THEOREM Spec => [](ABSpec_TypeOK /\ ABSpec_Inv)
=============================================================================