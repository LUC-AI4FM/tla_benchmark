---------------------------- MODULE MCSession11afair ----------------------------
EXTENDS Integers, Sequences

CONSTANTS Data

MCData == {"d1", "d2"}

VARIABLES AVar, BVar, AtoB, BtoA

vars == <<AVar, BVar, AtoB, BtoA>>

Bits == {0, 1}

Messages == Data \X Bits

RemoveAt(i, seq) ==
  [j \in 1..(Len(seq) - 1) |-> IF j < i THEN seq[j] ELSE seq[j + 1]]

-----------------------------------------------------------------------------

TypeOK ==
  /\ AVar \in Messages
  /\ BVar \in Messages
  /\ AtoB \in Seq(Messages)
  /\ BtoA \in Seq(Bits)

Init ==
  /\ AVar \in Data \X {1}
  /\ BVar = AVar
  /\ AtoB = << >>
  /\ BtoA = << >>

ASnd ==
  /\ AtoB' = Append(AtoB, AVar)
  /\ UNCHANGED <<AVar, BVar, BtoA>>

ARcv ==
  /\ BtoA # << >>
  /\ IF Head(BtoA) = AVar[2]
       THEN \E d \in Data : AVar' = <<d, 1 - AVar[2]>>
       ELSE AVar' = AVar
  /\ BtoA' = Tail(BtoA)
  /\ UNCHANGED <<BVar, AtoB>>

BSnd ==
  /\ BtoA' = Append(BtoA, BVar[2])
  /\ UNCHANGED <<AVar, BVar, AtoB>>

BRcv ==
  /\ AtoB # << >>
  /\ IF Head(AtoB)[2] # BVar[2]
       THEN BVar' = Head(AtoB)
       ELSE BVar' = BVar
  /\ AtoB' = Tail(AtoB)
  /\ UNCHANGED <<AVar, BtoA>>

LoseMsg ==
  /\ \/ /\ \E i \in 1..Len(AtoB) : AtoB' = RemoveAt(i, AtoB)
        /\ BtoA' = BtoA
     \/ /\ \E i \in 1..Len(BtoA) : BtoA' = RemoveAt(i, BtoA)
        /\ AtoB' = AtoB
  /\ UNCHANGED <<AVar, BVar>>

Next == ASnd \/ ARcv \/ BSnd \/ BRcv \/ LoseMsg

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ SF_vars(ARcv)
  /\ SF_vars(BRcv)
  /\ WF_vars(ASnd)
  /\ WF_vars(BSnd)

-----------------------------------------------------------------------------
(* State constraint bounding the message queues for model checking.        *)

SeqConstraint ==
  /\ Len(AtoB) \leq 3
  /\ Len(BtoA) \leq 3

(* Structural property of the channels.                                    *)

AtoBStructure ==
  /\ \A i \in 1..Len(AtoB) : AtoB[i] \in {AVar, BVar}
  /\ \A i, j \in 1..Len(AtoB) :
        (i < j /\ AtoB[i] = AVar) => AtoB[j] = AVar

BtoAStructure ==
  \A i \in 1..Len(BtoA) : BtoA[i] \in Bits

Inv ==
  /\ TypeOK
  /\ AtoBStructure
  /\ BtoAStructure

-----------------------------------------------------------------------------
(* High-level ABSpec, exposed as the property ABSpecProperty.             *)

ABInit ==
  /\ AVar \in Data \X {1}
  /\ BVar = AVar

ABA ==
  /\ AVar = BVar
  /\ \E d \in Data : AVar' = <<d, 1 - AVar[2]>>
  /\ BVar' = BVar

ABB ==
  /\ AVar # BVar
  /\ BVar' = AVar
  /\ AVar' = AVar

ABNext == ABA \/ ABB

ABSpecProperty ==
  /\ ABInit
  /\ [][ABNext]_<<AVar, BVar>>
  /\ WF_<<AVar, BVar>>(ABNext)

THEOREM Spec => [](Inv) /\ ABSpecProperty
=============================================================================