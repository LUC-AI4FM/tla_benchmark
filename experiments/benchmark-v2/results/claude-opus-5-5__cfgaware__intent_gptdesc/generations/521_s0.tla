--------------------------------- MODULE AB ---------------------------------
EXTENDS Integers, Sequences

CONSTANT Data

VARIABLES AVar, BVar, AtoB, BtoA

vars == <<AVar, BVar, AtoB, BtoA>>

Bits == {0, 1}

MaxLen == 3

ConstData == {"d1", "d2"}

-----------------------------------------------------------------------------
AB_TypeOK == /\ AVar \in Data \X Bits
             /\ BVar \in Data \X Bits
             /\ AtoB \in Seq(Data \X Bits)
             /\ BtoA \in Seq(Bits)

Init == /\ AVar \in Data \X {1}
        /\ BVar = AVar
        /\ AtoB = << >>
        /\ BtoA = << >>

ASnd == /\ AtoB' = Append(AtoB, AVar)
        /\ UNCHANGED <<AVar, BVar, BtoA>>

ARcv == /\ BtoA # << >>
        /\ IF Head(BtoA) = AVar[2]
             THEN \E d \in Data : AVar' = <<d, 1 - AVar[2]>>
             ELSE AVar' = AVar
        /\ BtoA' = Tail(BtoA)
        /\ UNCHANGED <<BVar, AtoB>>

BSnd == /\ BtoA' = Append(BtoA, BVar[2])
        /\ UNCHANGED <<AVar, BVar, AtoB>>

BRcv == /\ AtoB # << >>
        /\ IF Head(AtoB)[2] # BVar[2]
             THEN BVar' = Head(AtoB)
             ELSE BVar' = BVar
        /\ AtoB' = Tail(AtoB)
        /\ UNCHANGED <<AVar, BtoA>>

Next == ASnd \/ ARcv \/ BSnd \/ BRcv

Spec == /\ Init
        /\ [][Next]_vars
        /\ WF_vars(ASnd)
        /\ WF_vars(ARcv)
        /\ WF_vars(BSnd)
        /\ WF_vars(BRcv)

-----------------------------------------------------------------------------
StateConstraint == /\ Len(AtoB) =< MaxLen
                   /\ Len(BtoA) =< MaxLen

TwoRuns(s) ==
  \E i \in 0..Len(s) :
     /\ \A j, k \in 1..i : s[j] = s[k]
     /\ \A j, k \in (i+1)..Len(s) : s[j] = s[k]

AB_TwoValsSeq == /\ TwoRuns(AtoB)
                 /\ TwoRuns(BtoA)

AB_Inv == /\ AB_TypeOK
           /\ ((BtoA # << >>) /\ (Head(BtoA) = AVar[2])) => (AVar = BVar)
           /\ AB_TwoValsSeq

-----------------------------------------------------------------------------
(* Abstract specification of the exchange, used as a refinement property. *)
ABS_Init == /\ AVar \in Data \X {1}
            /\ BVar = AVar

ABS_A == /\ AVar = BVar
         /\ \E d \in Data : AVar' = <<d, 1 - AVar[2]>>
         /\ BVar' = BVar

ABS_B == /\ AVar # BVar
         /\ BVar' = AVar
         /\ AVar' = AVar

ABS_Next == ABS_A \/ ABS_B

ABSpecProperty == ABS_Init /\ [][ABS_Next]_<<AVar, BVar>>
=============================================================================