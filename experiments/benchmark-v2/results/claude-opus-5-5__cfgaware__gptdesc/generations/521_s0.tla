------------------------------- MODULE MCSession11 -------------------------------
EXTENDS Integers, Sequences

CONSTANT Data

VARIABLES AVar, BVar, AtoB, BtoA

vars == <<AVar, BVar, AtoB, BtoA>>

-----------------------------------------------------------------------------
(* Concrete constant data, used to override Data in the model *)
ConstData == {"d1", "d2"}

(* Bound the lengths of the message queues *)
StateConstraint == /\ Len(AtoB) <= 3
                   /\ Len(BtoA) <= 3

-----------------------------------------------------------------------------
(* Alternating bit protocol (the session module being wrapped) *)

Bits == {0, 1}

RemoveAt(s, i) == [j \in 1..(Len(s) - 1) |-> IF j < i THEN s[j] ELSE s[j + 1]]

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

LoseMsg == \/ /\ \E i \in 1..Len(AtoB) : AtoB' = RemoveAt(AtoB, i)
              /\ UNCHANGED <<AVar, BVar, BtoA>>
           \/ /\ \E i \in 1..Len(BtoA) : BtoA' = RemoveAt(BtoA, i)
              /\ UNCHANGED <<AVar, BVar, AtoB>>

Next == ASnd \/ ARcv \/ BSnd \/ BRcv \/ LoseMsg

Spec == /\ Init
        /\ [][Next]_vars
        /\ WF_vars(ASnd)
        /\ WF_vars(BSnd)
        /\ SF_vars(ARcv)
        /\ SF_vars(BRcv)

-----------------------------------------------------------------------------
(* Derived predicates about the communication variables and channels *)

AB_TypeOK == /\ AVar \in Data \X Bits
             /\ BVar \in Data \X Bits
             /\ AtoB \in Seq(Data \X Bits)
             /\ BtoA \in Seq(Bits)

AB_Inv == /\ AB_TypeOK
          /\ (AVar[2] = BVar[2]) => (AVar = BVar)
          /\ \A i \in 1..Len(AtoB) : (AtoB[i][2] = AVar[2]) => (AtoB[i] = AVar)
          /\ \A i \in 1..Len(BtoA) : (BtoA[i] = AVar[2]) => (BVar = AVar)

IsTwoValsSeq(s) ==
    \A i, j \in 1..(Len(s) - 1) :
        (s[i] # s[i + 1] /\ s[j] # s[j + 1]) => (i = j)

AtoBBits == [i \in 1..Len(AtoB) |-> AtoB[i][2]]

AB_TwoValsSeq == /\ IsTwoValsSeq(AtoBBits)
                 /\ IsTwoValsSeq(BtoA)

-----------------------------------------------------------------------------
(* Fair high-level specification (Session11afair) *)

ABS_Init == /\ AVar \in Data \X {1}
            /\ BVar = AVar

ABS_A == /\ AVar = BVar
         /\ \E d \in Data : AVar' = <<d, 1 - AVar[2]>>
         /\ BVar' = BVar

ABS_B == /\ AVar # BVar
         /\ BVar' = AVar
         /\ AVar' = AVar

ABS_Next == ABS_A \/ ABS_B

ABS_vars == <<AVar, BVar>>

ABS_Spec == /\ ABS_Init
            /\ [][ABS_Next]_ABS_vars
            /\ WF_ABS_vars(ABS_A)
            /\ WF_ABS_vars(ABS_B)

ABSpecProperty == ABS_Spec

=============================================================================