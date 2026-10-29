------------------------------ MODULE ABQueue ------------------------------
EXTENDS Integers, Sequences

CONSTANT Data

VARIABLES AVar, BVar, AtoB, BtoA, NewValQueue

vars == << AVar, BVar, AtoB, BtoA, NewValQueue >>

Msgs == (Data \X {0, 1}) \cup {0, 1}

E == /\ Len(AtoB) <= 3
     /\ Len(BtoA) <= 3
     /\ Len(NewValQueue) <= 1

TypeOK == /\ AVar \in Data \X {0, 1}
          /\ BVar \in Data \X {0, 1}
          /\ AtoB \in Seq(Data \X {0, 1})
          /\ BtoA \in Seq({0, 1})
          /\ NewValQueue \in Seq(Data)

Init == /\ AVar \in Data \X {1}
        /\ BVar = AVar
        /\ AtoB = << >>
        /\ BtoA = << >>
        /\ NewValQueue = << >>

ASnd == /\ AtoB' = Append(AtoB, AVar)
        /\ UNCHANGED << AVar, BVar, BtoA, NewValQueue >>

ARcv == /\ BtoA /= << >>
        /\ BtoA' = Tail(BtoA)
        /\ IF /\ Head(BtoA) = AVar[2]
              /\ NewValQueue /= << >>
             THEN /\ AVar' = << Head(NewValQueue), 1 - AVar[2] >>
                  /\ NewValQueue' = Tail(NewValQueue)
             ELSE UNCHANGED << AVar, NewValQueue >>
        /\ UNCHANGED << BVar, AtoB >>

BSnd == /\ BtoA' = Append(BtoA, BVar[2])
        /\ UNCHANGED << AVar, BVar, AtoB, NewValQueue >>

BRcv == /\ AtoB /= << >>
        /\ AtoB' = Tail(AtoB)
        /\ IF Head(AtoB)[2] /= BVar[2]
             THEN BVar' = Head(AtoB)
             ELSE BVar' = BVar
        /\ UNCHANGED << AVar, BtoA, NewValQueue >>

RemoveElt(i, seq) ==
  [j \in 1..(Len(seq) - 1) |-> IF j < i THEN seq[j] ELSE seq[j + 1]]

LoseMsgAtoB == /\ AtoB /= << >>
               /\ \E i \in 1..Len(AtoB) : AtoB' = RemoveElt(i, AtoB)
               /\ UNCHANGED << AVar, BVar, BtoA, NewValQueue >>

LoseMsgBtoA == /\ BtoA /= << >>
               /\ \E i \in 1..Len(BtoA) : BtoA' = RemoveElt(i, BtoA)
               /\ UNCHANGED << AVar, BVar, AtoB, NewValQueue >>

NewVal == /\ AVar = BVar
           /\ NewValQueue = << >>
           /\ \E d \in Data : NewValQueue' = Append(NewValQueue, d)
           /\ UNCHANGED << AVar, BVar, AtoB, BtoA >>

Next == \/ ASnd
        \/ ARcv
        \/ BSnd
        \/ BRcv
        \/ LoseMsgAtoB
        \/ LoseMsgBtoA
        \/ NewVal

Spec == /\ Init
        /\ [][Next]_vars
        /\ WF_vars(ASnd)
        /\ WF_vars(BSnd)
        /\ SF_vars(ARcv)
        /\ SF_vars(BRcv)
        /\ WF_vars(NewVal)

=============================================================================