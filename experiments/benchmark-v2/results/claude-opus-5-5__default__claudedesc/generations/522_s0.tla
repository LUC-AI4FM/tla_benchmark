---------------------------- MODULE AlternatingBit ----------------------------
EXTENDS Integers, Sequences

CONSTANT Data

VARIABLES AVar, BVar, AtoB, BtoA

vars == << AVar, BVar, AtoB, BtoA >>

Bits == {0, 1}

Msgs == [data : Data, bit : Bits]

RemoveElt(i, seq) ==
    [j \in 1..(Len(seq) - 1) |-> IF j < i THEN seq[j] ELSE seq[j + 1]]

TypeOK ==
    /\ AVar \in Msgs
    /\ BVar \in Msgs
    /\ AtoB \in Seq(Msgs)
    /\ BtoA \in Seq(Bits)

Init ==
    /\ AVar \in [data : Data, bit : {1}]
    /\ BVar = AVar
    /\ AtoB = << >>
    /\ BtoA = << >>

ASend ==
    /\ AtoB' = Append(AtoB, AVar)
    /\ UNCHANGED << AVar, BVar, BtoA >>

ARecv ==
    /\ BtoA /= << >>
    /\ IF Head(BtoA) = AVar.bit
          THEN \E d \in Data : AVar' = [data |-> d, bit |-> 1 - AVar.bit]
          ELSE AVar' = AVar
    /\ BtoA' = Tail(BtoA)
    /\ UNCHANGED << BVar, AtoB >>

BSend ==
    /\ BtoA' = Append(BtoA, BVar.bit)
    /\ UNCHANGED << AVar, BVar, AtoB >>

BRecv ==
    /\ AtoB /= << >>
    /\ IF Head(AtoB).bit /= BVar.bit
          THEN BVar' = Head(AtoB)
          ELSE BVar' = BVar
    /\ AtoB' = Tail(AtoB)
    /\ UNCHANGED << AVar, BtoA >>

LoseMsgs ==
    /\ \/ /\ \E i \in 1..Len(AtoB) : AtoB' = RemoveElt(i, AtoB)
          /\ BtoA' = BtoA
       \/ /\ \E i \in 1..Len(BtoA) : BtoA' = RemoveElt(i, BtoA)
          /\ AtoB' = AtoB
    /\ UNCHANGED << AVar, BVar >>

Next ==
    \/ ASend
    \/ ARecv
    \/ BSend
    \/ BRecv
    \/ LoseMsgs

Fairness ==
    /\ WF_vars(ASend)
    /\ WF_vars(BSend)
    /\ SF_vars(ARecv)
    /\ SF_vars(BRecv)

Spec == Init /\ [][Next]_vars /\ Fairness

=============================================================================