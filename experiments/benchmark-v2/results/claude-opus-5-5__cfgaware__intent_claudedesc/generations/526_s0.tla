------------------------------- MODULE ABSpec -------------------------------
EXTENDS Integers, Sequences

CONSTANT Data

VARIABLES AVar, BVar, NewValQueue

vars == <<AVar, BVar, NewValQueue>>

Msgs == Data \X {0, 1}

TypeOK == /\ AVar \in Msgs
          /\ BVar \in Msgs
          /\ NewValQueue \in Seq(Data)

Init == /\ AVar \in Data \X {1}
        /\ BVar = AVar
        /\ NewValQueue = << >>

E == /\ AVar = BVar
     /\ NewValQueue = << >>
     /\ \E d \in Data : NewValQueue' = Append(NewValQueue, d)
     /\ UNCHANGED <<AVar, BVar>>

A == /\ AVar = BVar
     /\ NewValQueue # << >>
     /\ AVar' = << Head(NewValQueue), 1 - AVar[2] >>
     /\ NewValQueue' = Tail(NewValQueue)
     /\ UNCHANGED BVar

B == /\ AVar[2] # BVar[2]
     /\ BVar' = AVar
     /\ UNCHANGED <<AVar, NewValQueue>>

Next == E \/ A \/ B

Spec == /\ Init
        /\ [][Next]_vars
        /\ WF_vars(A)
        /\ WF_vars(B)

Inv == AVar[2] = BVar[2] => AVar = BVar

=============================================================================