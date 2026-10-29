---------------------------- MODULE ABSpec ----------------------------
EXTENDS Naturals

CONSTANT Data

VARIABLES AVar, BVar

vars == <<AVar, BVar>>

ConstData == {"d1", "d2"}

ABSpec_TypeOK ==
    /\ AVar \in Data \X {0, 1}
    /\ BVar \in Data \X {0, 1}

Init ==
    /\ AVar \in Data \X {1}
    /\ BVar = AVar

A ==
    /\ AVar = BVar
    /\ \E d \in Data : AVar' = <<d, 1 - AVar[2]>>
    /\ UNCHANGED BVar

B ==
    /\ AVar # BVar
    /\ BVar' = AVar
    /\ UNCHANGED AVar

Next == A \/ B

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

ABSpec_Inv == (AVar[2] = BVar[2]) => (AVar = BVar)

InfinitelyAlternating ==
    /\ []<>(AVar = BVar)
    /\ []<>(AVar # BVar)

Liveness == (AVar # BVar) ~> (AVar = BVar)

=============================================================================