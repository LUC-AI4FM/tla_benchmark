---------------------------- MODULE MCSession11b ----------------------------
EXTENDS Integers, Sequences, FiniteSets

(***************************************************************************)
(* Model-checking configuration for the Alternating Bit Protocol           *)
(* (Session11b), which refines the high-level spec ABSpec (Session11a).   *)
(***************************************************************************)

\* Concrete instantiation of the Data constant
Data == {"Fred", "Mary", "Ted"}

VARIABLES AVar, BVar, AtoB, BtoA

vars == <<AVar, BVar, AtoB, BtoA>>

Messages == Data \X {0, 1}

Remove(i, seq) ==
    [j \in 1..(Len(seq) - 1) |-> IF j < i THEN seq[j] ELSE seq[j + 1]]

-----------------------------------------------------------------------------
(* Alternating Bit Protocol (Session11b)                                    *)

ABInit ==
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
    /\ \/ /\ \E i \in 1..Len(AtoB) : AtoB' = Remove(i, AtoB)
          /\ BtoA' = BtoA
       \/ /\ \E i \in 1..Len(BtoA) : BtoA' = Remove(i, BtoA)
          /\ AtoB' = AtoB
    /\ UNCHANGED <<AVar, BVar>>

Next == ASnd \/ ARcv \/ BSnd \/ BRcv \/ LoseMsg

Spec ==
    /\ ABInit
    /\ [][Next]_vars
    /\ WF_vars(ASnd)
    /\ WF_vars(BSnd)
    /\ SF_vars(ARcv)
    /\ SF_vars(BRcv)

Init == ABInit

-----------------------------------------------------------------------------
(* Invariants                                                               *)

AB_TypeOK ==
    /\ AVar \in Messages
    /\ BVar \in Messages
    /\ AtoB \in Seq(Messages)
    /\ BtoA \in Seq({0, 1})

AB_Inv ==
    (BtoA # << >> /\ Head(BtoA) = AVar[2]) => (AVar = BVar)

TwoValsSeq(s) ==
    Cardinality({i \in 1..(Len(s) - 1) : s[i] # s[i + 1]}) <= 1

AB_TwoValsSeq ==
    /\ TwoValsSeq(AtoB)
    /\ TwoValsSeq(BtoA)

-----------------------------------------------------------------------------
(* State constraint bounding channel lengths                                *)

SeqConstraint ==
    /\ Len(AtoB) <= 3
    /\ Len(BtoA) <= 3

-----------------------------------------------------------------------------
(* High-level specification ABSpec (Session11a), for refinement checking   *)

HLInit ==
    /\ AVar \in Data \X {1}
    /\ BVar = AVar

HLA ==
    /\ AVar = BVar
    /\ \E d \in Data : AVar' = <<d, 1 - AVar[2]>>
    /\ BVar' = BVar

HLB ==
    /\ AVar # BVar
    /\ BVar' = AVar
    /\ AVar' = AVar

HLNext == HLA \/ HLB

ABSpec ==
    /\ HLInit
    /\ [][HLNext]_<<AVar, BVar>>
    /\ WF_<<AVar, BVar>>(HLNext)

\* Temporal property: the protocol implements ABSpec
ABSpecProperty == ABSpec

THEOREM Spec => [](AB_TypeOK /\ AB_Inv /\ AB_TwoValsSeq)
THEOREM Spec => ABSpecProperty
=============================================================================