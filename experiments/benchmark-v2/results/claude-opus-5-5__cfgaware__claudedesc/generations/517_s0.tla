------------------------------ MODULE MCSession11b ------------------------------
EXTENDS Integers, Sequences, FiniteSets

CONSTANT Data

VARIABLES AVar, BVar, AtoB, BtoA

vars == <<AVar, BVar, AtoB, BtoA>>

ConstData == {"Fred", "Mary", "Ted"}

-----------------------------------------------------------------------------
Message == Data \X {0, 1}

RemoveAt(i, seq) == [j \in 1..(Len(seq) - 1) |-> IF j < i THEN seq[j] ELSE seq[j + 1]]

Init == /\ AVar \in Data \X {1}
        /\ BVar = AVar
        /\ AtoB = << >>
        /\ BtoA = << >>

ASnd == /\ AtoB' = Append(AtoB, AVar)
        /\ UNCHANGED <<AVar, BVar, BtoA>>

ARcv == /\ BtoA /= << >>
        /\ IF Head(BtoA) = AVar[2]
             THEN \E d \in Data : AVar' = <<d, 1 - AVar[2]>>
             ELSE AVar' = AVar
        /\ BtoA' = Tail(BtoA)
        /\ UNCHANGED <<BVar, AtoB>>

BSnd == /\ BtoA' = Append(BtoA, BVar[2])
        /\ UNCHANGED <<AVar, BVar, AtoB>>

BRcv == /\ AtoB /= << >>
        /\ IF Head(AtoB)[2] /= BVar[2]
             THEN BVar' = Head(AtoB)
             ELSE BVar' = BVar
        /\ AtoB' = Tail(AtoB)
        /\ UNCHANGED <<AVar, BtoA>>

LoseMsg == \/ /\ \E i \in 1..Len(AtoB) : AtoB' = RemoveAt(i, AtoB)
              /\ UNCHANGED <<AVar, BVar, BtoA>>
           \/ /\ \E i \in 1..Len(BtoA) : BtoA' = RemoveAt(i, BtoA)
              /\ UNCHANGED <<AVar, BVar, AtoB>>

Next == ASnd \/ ARcv \/ BSnd \/ BRcv \/ LoseMsg

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
StateConstraint == Len(AtoB) <= 3 /\ Len(BtoA) <= 3

AB_TypeOK == /\ AVar \in Message
             /\ BVar \in Message
             /\ AtoB \in Seq(Message)
             /\ BtoA \in Seq({0, 1})

AB_Inv == (BtoA /= << >> /\ Head(BtoA) = AVar[2]) => (AVar = BVar)

TwoValsSeq(s) ==
    \A i, j \in 1..(Len(s) - 1) :
        (s[i] /= s[i + 1] /\ s[j] /= s[j + 1]) => i = j

AB_TwoValsSeq == TwoValsSeq(AtoB) /\ TwoValsSeq(BtoA)

-----------------------------------------------------------------------------
(* High-level specification ABSpec (as in Session11a), over AVar and BVar. *)
ABInit == /\ AVar \in Data \X {1}
          /\ BVar = AVar

ABA == /\ AVar = BVar
       /\ \E d \in Data : AVar' = <<d, 1 - AVar[2]>>
       /\ BVar' = BVar

ABB == /\ AVar /= BVar
       /\ BVar' = AVar
       /\ AVar' = AVar

ABNext == ABA \/ ABB

ABSpec == ABInit /\ [][ABNext]_<<AVar, BVar>>

ABSpecProperty == ABSpec
=============================================================================