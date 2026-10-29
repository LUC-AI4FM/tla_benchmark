------------------------------- MODULE AlternatingBit -------------------------------
EXTENDS Naturals, Sequences

CONSTANT Data

VARIABLES AVar, BVar, AtoB, BtoA

vars == <<AVar, BVar, AtoB, BtoA>>

Msgs == [data : Data, bit : {0, 1}]

RemoveAt(s, i) == SubSeq(s, 1, i - 1) \o SubSeq(s, i + 1, Len(s))

Init ==
    /\ AVar \in Msgs
    /\ AVar.bit = 1
    /\ BVar = AVar
    /\ AtoB = << >>
    /\ BtoA = << >>

ASend ==
    /\ AtoB' = Append(AtoB, AVar)
    /\ UNCHANGED <<AVar, BVar, BtoA>>

ARecv ==
    /\ BtoA # << >>
    /\ IF Head(BtoA) = AVar.bit
         THEN \E d \in Data : AVar' = [data |-> d, bit |-> 1 - AVar.bit]
         ELSE AVar' = AVar
    /\ BtoA' = Tail(BtoA)
    /\ UNCHANGED <<BVar, AtoB>>

BSend ==
    /\ BtoA' = Append(BtoA, BVar.bit)
    /\ UNCHANGED <<AVar, BVar, AtoB>>

BRecv ==
    /\ AtoB # << >>
    /\ IF Head(AtoB).bit # BVar.bit
         THEN BVar' = Head(AtoB)
         ELSE BVar' = BVar
    /\ AtoB' = Tail(AtoB)
    /\ UNCHANGED <<AVar, BtoA>>

LoseMsgs ==
    \/ /\ \E i \in 1..Len(AtoB) : AtoB' = RemoveAt(AtoB, i)
       /\ UNCHANGED <<AVar, BVar, BtoA>>
    \/ /\ \E i \in 1..Len(BtoA) : BtoA' = RemoveAt(BtoA, i)
       /\ UNCHANGED <<AVar, BVar, AtoB>>

Next == ASend \/ ARecv \/ BSend \/ BRecv \/ LoseMsgs

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(ASend)
    /\ WF_vars(BSend)
    /\ SF_vars(ARecv)
    /\ SF_vars(BRecv)

TypeOK ==
    /\ AVar \in Msgs
    /\ BVar \in Msgs
    /\ AtoB \in Seq(Msgs)
    /\ BtoA \in Seq({0, 1})

=====================================================================================