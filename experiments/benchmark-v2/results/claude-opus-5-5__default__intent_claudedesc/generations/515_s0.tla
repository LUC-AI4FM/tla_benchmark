---------------------------- MODULE AlternatingBit ----------------------------
EXTENDS Naturals

CONSTANT Data

VARIABLES AVar, BVar

vars == <<AVar, BVar>>

Bits == {0, 1}

TypeOK ==
    /\ AVar \in Data \X Bits
    /\ BVar \in Data \X Bits

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

-----------------------------------------------------------------------------

Inv == (AVar[2] = BVar[2]) => (AVar = BVar)

Liveness == (AVar # BVar) ~> (AVar = BVar)

InfiniteAlternation == []<>(AVar = BVar) /\ []<>(AVar # BVar)

FairSpec == Spec

THEOREM Spec => [](TypeOK /\ Inv)
THEOREM Spec => Liveness
THEOREM Spec => InfiniteAlternation
=============================================================================