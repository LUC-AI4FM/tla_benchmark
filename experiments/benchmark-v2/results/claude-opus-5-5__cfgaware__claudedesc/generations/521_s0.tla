---------------------------- MODULE MCSession11d ----------------------------
EXTENDS Integers, Sequences

CONSTANT Data

VARIABLES AVar, BVar, AtoB, BtoA

vars == <<AVar, BVar, AtoB, BtoA>>

ConstData == {"Fred", "Mary", "Ted"}

RemoveIth(s, i) == [j \in 1..(Len(s) - 1) |-> IF j < i THEN s[j] ELSE s[j + 1]]

-----------------------------------------------------------------------------
(* Alternating Bit Protocol implementation (Session11d) *)

Init == /\ AVar \in Data \X {1}
        /\ BVar = AVar
        /\ AtoB = << >>
        /\ BtoA = << >>

ASnd == /\ AtoB' = Append(AtoB, AVar)
        /\ UNCHANGED <<AVar, BtoA, BVar>>

ARcv == /\ BtoA /= << >>
        /\ IF Head(BtoA) = AVar[2]
             THEN \E d \in Data : AVar' = <<d, 1 - AVar[2]>>
             ELSE AVar' = AVar
        /\ BtoA' = Tail(BtoA)
        /\ UNCHANGED <<AtoB, BVar>>

BSnd == /\ BtoA' = Append(BtoA, BVar[2])
        /\ UNCHANGED <<AVar, BVar, AtoB>>

BRcv == /\ AtoB /= << >>
        /\ IF Head(AtoB)[2] /= BVar[2]
             THEN BVar' = Head(AtoB)
             ELSE BVar' = BVar
        /\ AtoB' = Tail(AtoB)
        /\ UNCHANGED <<AVar, BtoA>>

LoseMsg == /\ \/ /\ \E i \in 1..Len(AtoB) : AtoB' = RemoveIth(AtoB, i)
                 /\ BtoA' = BtoA
              \/ /\ \E i \in 1..Len(BtoA) : BtoA' = RemoveIth(BtoA, i)
                 /\ AtoB' = AtoB
           /\ UNCHANGED <<AVar, BVar>>

Next == ASnd \/ ARcv \/ BSnd \/ BRcv \/ LoseMsg

Spec == /\ Init
        /\ [][Next]_vars
        /\ SF_vars(ARcv)
        /\ SF_vars(BRcv)
        /\ WF_vars(ASnd)
        /\ WF_vars(BSnd)

-----------------------------------------------------------------------------
(* Model-checking definitions *)

StateConstraint == /\ Len(AtoB) <= 3
                   /\ Len(BtoA) <= 3

Messages == Data \X {0, 1}

AB_TypeOK == /\ AVar \in Messages
             /\ BVar \in Messages
             /\ AtoB \in Seq(Messages)
             /\ BtoA \in Seq({0, 1})

AB_Inv == (BtoA /= << >> /\ Head(BtoA) = AVar[2]) => (AVar = BVar)

IsTwoValSeq(s) ==
    \A i, j \in 1..(Len(s) - 1) :
        (s[i] /= s[i + 1] /\ s[j] /= s[j + 1]) => (i = j)

BitsOf(s) == [i \in 1..Len(s) |-> s[i][2]]

AB_TwoValsSeq == /\ IsTwoValSeq(AtoB)
                 /\ IsTwoValSeq(BitsOf(AtoB))
                 /\ IsTwoValSeq(BtoA)

-----------------------------------------------------------------------------
(* Abstract fair specification (Session11afair), instantiated as ABSpec *)

ABS_Init == /\ AVar \in Data \X {1}
            /\ BVar = AVar

ABS_A == /\ AVar = BVar
         /\ \E d \in Data : AVar' = <<d, 1 - AVar[2]>>
         /\ BVar' = BVar

ABS_B == /\ AVar /= BVar
         /\ BVar' = AVar
         /\ AVar' = AVar

ABS_Next == ABS_A \/ ABS_B

ABS_FairSpec == /\ ABS_Init
                /\ [][ABS_Next]_<<AVar, BVar>>
                /\ WF_<<AVar, BVar>>(ABS_Next)

ABSpecProperty == ABS_FairSpec

=============================================================================