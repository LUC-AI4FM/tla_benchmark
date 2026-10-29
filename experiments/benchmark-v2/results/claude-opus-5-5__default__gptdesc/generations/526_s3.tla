---------------------------- MODULE ABSpec ----------------------------
EXTENDS Integers, Sequences

CONSTANT Data

VARIABLES AVar, BVar, NewValQueue

vars == << AVar, BVar, NewValQueue >>

TypeOK == /\ AVar \in Data \X {0, 1}
          /\ BVar \in Data \X {0, 1}
          /\ NewValQueue \in Seq(Data)

Init == /\ AVar \in Data \X {1}
        /\ BVar = AVar
        /\ NewValQueue = << >>

A == /\ AVar = BVar
     /\ NewValQueue # << >>
     /\ AVar' = << Head(NewValQueue), 1 - AVar[2] >>
     /\ NewValQueue' = Tail(NewValQueue)
     /\ BVar' = BVar

B == /\ AVar # BVar
     /\ BVar' = AVar
     /\ UNCHANGED << AVar, NewValQueue >>

E == /\ \E d \in Data : NewValQueue' = Append(NewValQueue, d)
     /\ UNCHANGED << AVar, BVar >>

Next == A \/ B \/ E

Spec == Init /\ [][Next]_vars /\ WF_vars(A) /\ WF_vars(B)

-----------------------------------------------------------------------------

BitConsistency == (AVar[2] = BVar[2]) => (AVar = BVar)

Delivery == (AVar # BVar) ~> (AVar = BVar)

QueueConsumed == (NewValQueue # << >>) ~> (AVar = BVar /\ NewValQueue = << >>) \/ (AVar # BVar)

=============================================================================