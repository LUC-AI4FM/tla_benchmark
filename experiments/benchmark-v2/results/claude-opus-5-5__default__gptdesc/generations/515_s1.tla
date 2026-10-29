---------------------------- MODULE MCSession11afair ----------------------------
EXTENDS Naturals

CONSTANT Data

VARIABLES AVar, BVar

vars == <<AVar, BVar>>

MCData == {"d1", "d2", "d3"}

Init == /\ AVar \in Data \X {1}
        /\ BVar = AVar

A == /\ AVar = BVar
     /\ \E d \in Data : AVar' = <<d, 1 - AVar[2]>>
     /\ UNCHANGED BVar

B == /\ AVar # BVar
     /\ BVar' = AVar
     /\ UNCHANGED AVar

Next == A \/ B

Spec == Init /\ [][Next]_vars

FairSpec == Spec /\ WF_vars(Next)

TypeOK == /\ AVar \in Data \X {0, 1}
          /\ BVar \in Data \X {0, 1}

Inv == (AVar[2] = BVar[2]) <=> (AVar = BVar)

Agreement == \A v \in Data \X {0, 1} : (AVar = v) ~> (BVar = v)

EventuallyAgree == []<>(AVar = BVar)

Alternation == /\ []<>(AVar = BVar)
               /\ []<>(AVar # BVar)

THEOREM FairSpec => [](TypeOK /\ Inv)
THEOREM FairSpec => Agreement /\ EventuallyAgree /\ Alternation
=============================================================================