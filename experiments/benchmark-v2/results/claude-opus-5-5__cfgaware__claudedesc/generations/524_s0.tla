------------------------------ MODULE ABP ------------------------------
EXTENDS Integers, Sequences

CONSTANT Data

VARIABLES AVar, BVar, NewValQueue, AtoB, BtoA

vars == << AVar, BVar, NewValQueue, AtoB, BtoA >>

Msgs == [data : Data, bit : {0, 1}]

RemoveAt(s, i) ==
  [j \in 1..(Len(s) - 1) |-> IF j < i THEN s[j] ELSE s[j + 1]]

TypeOK ==
  /\ AVar \in Msgs
  /\ BVar \in Msgs
  /\ NewValQueue \in Seq(Data)
  /\ AtoB \in Seq(Msgs)
  /\ BtoA \in Seq({0, 1})

Init ==
  /\ AVar \in Msgs
  /\ BVar = AVar
  /\ NewValQueue = << >>
  /\ AtoB = << >>
  /\ BtoA = << >>

ASend ==
  /\ AtoB' = Append(AtoB, AVar)
  /\ UNCHANGED << AVar, BVar, NewValQueue, BtoA >>

ARecv ==
  /\ BtoA # << >>
  /\ IF Head(BtoA) = AVar.bit
       THEN /\ NewValQueue # << >>
            /\ AVar' = [data |-> Head(NewValQueue), bit |-> 1 - AVar.bit]
            /\ NewValQueue' = Tail(NewValQueue)
       ELSE UNCHANGED << AVar, NewValQueue >>
  /\ BtoA' = Tail(BtoA)
  /\ UNCHANGED << BVar, AtoB >>

BSend ==
  /\ BtoA' = Append(BtoA, BVar.bit)
  /\ UNCHANGED << AVar, BVar, NewValQueue, AtoB >>

BRecv ==
  /\ AtoB # << >>
  /\ IF Head(AtoB).bit # BVar.bit
       THEN BVar' = Head(AtoB)
       ELSE UNCHANGED BVar
  /\ AtoB' = Tail(AtoB)
  /\ UNCHANGED << AVar, NewValQueue, BtoA >>

LoseMsgs ==
  /\ \/ /\ \E i \in 1..Len(AtoB) : AtoB' = RemoveAt(AtoB, i)
        /\ UNCHANGED BtoA
     \/ /\ \E i \in 1..Len(BtoA) : BtoA' = RemoveAt(BtoA, i)
        /\ UNCHANGED AtoB
  /\ UNCHANGED << AVar, BVar, NewValQueue >>

E ==
  /\ AVar = BVar
  /\ \E d \in Data : NewValQueue' = Append(NewValQueue, d)
  /\ UNCHANGED << AVar, BVar, AtoB, BtoA >>

Next == ASend \/ ARecv \/ BSend \/ BRecv \/ LoseMsgs \/ E

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(ASend)
  /\ WF_vars(BSend)
  /\ SF_vars(ARecv)
  /\ SF_vars(BRecv)

=============================================================================