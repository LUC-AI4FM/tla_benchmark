------------------------------- MODULE MCAB -------------------------------
(***************************************************************************)
(* Model-checking configuration for the Alternating Bit Protocol from     *)
(* Session11d, checked against the fair abstract specification from       *)
(* Session11afair.                                                         *)
(*                                                                         *)
(* This module is self-contained so that it passes SANY on its own.       *)
(* - The protocol definitions (Session11d) are inlined below.             *)
(* - The abstract fair specification (Session11afair) is inlined below.   *)
(*   It is the ABSpec_* definitions, which play the role of               *)
(*   ABSpec == INSTANCE Session11afair.                                    *)
(*                                                                         *)
(* TLC configuration:                                                      *)
(*   CONSTANT Data <- const_Data                                           *)
(*   CONSTRAINT SeqConstraint                                              *)
(*   SPECIFICATION FairSpec                                                *)
(*   INVARIANTS AB_TypeOK AB_Inv AB_TwoValsSeq                             *)
(*   PROPERTY ABSpecProperty                                               *)
(***************************************************************************)
EXTENDS Integers, Sequences

CONSTANT Data

VARIABLES AVar,   \* sender's current message: <<data, bit>>
          BVar,   \* receiver's last received message: <<data, bit>>
          AtoB,   \* channel from A to B: sequence of <<data, bit>>
          BtoA    \* channel from B to A: sequence of bits

vars == <<AVar, BVar, AtoB, BtoA>>

---------------------------------------------------------------------------
(***************************************************************************)
(* Model values                                                            *)
(***************************************************************************)
const_Data == {"Fred", "Mary", "Ted"}

ASSUME Data = const_Data

\* State constraint: both channels hold at most three elements.
SeqConstraint == /\ Len(AtoB) <= 3
                 /\ Len(BtoA) <= 3

---------------------------------------------------------------------------
(***************************************************************************)
(* The Alternating Bit Protocol (Session11d)                              *)
(***************************************************************************)
Remove(i, s) == [j \in 1..(Len(s) - 1) |-> IF j < i THEN s[j] ELSE s[j + 1]]

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

LoseMsg == /\ \/ /\ \E i \in 1..Len(AtoB) : AtoB' = Remove(i, AtoB)
                 /\ BtoA' = BtoA
              \/ /\ \E i \in 1..Len(BtoA) : BtoA' = Remove(i, BtoA)
                 /\ AtoB' = AtoB
           /\ UNCHANGED <<AVar, BVar>>

Next == ASnd \/ ARcv \/ BSnd \/ BRcv \/ LoseMsg

Spec == Init /\ [][Next]_vars

FairSpec == /\ Spec
            /\ WF_vars(ASnd)
            /\ WF_vars(BSnd)
            /\ SF_vars(ARcv)
            /\ SF_vars(BRcv)

---------------------------------------------------------------------------
(***************************************************************************)
(* Invariants                                                              *)
(***************************************************************************)
AB_TypeOK == /\ AVar \in Data \X {0, 1}
             /\ BVar \in Data \X {0, 1}
             /\ AtoB \in Seq(Data \X {0, 1})
             /\ BtoA \in Seq({0, 1})

AB_Inv == (BtoA # << >>) /\ (Head(BtoA) = AVar[2]) => (AVar = BVar)

\* A sequence consists of a run of one value followed by a run of
\* another value: there is at most one point i where s[i] # s[i+1].
IsTwoValSeq(s) ==
    \E k \in 0..Len(s) :
        \A i \in 1..Len(s) :
            s[i] = IF i <= k THEN s[1] ELSE s[Len(s)]

AB_TwoValsSeq == /\ IsTwoValSeq(AtoB)
                 /\ IsTwoValSeq(BtoA)

---------------------------------------------------------------------------
(***************************************************************************)
(* Abstract fair specification (Session11afair), playing the role of     *)
(*   ABSpec == INSTANCE Session11afair                                     *)
(***************************************************************************)
ABSpec_vars == <<AVar, BVar>>

ABSpec_Init == /\ AVar \in Data \X {1}
               /\ BVar = AVar

ABSpec_A == /\ AVar = BVar
            /\ \E d \in Data : AVar' = <<d, 1 - AVar[2]>>
            /\ BVar' = BVar

ABSpec_B == /\ AVar # BVar
            /\ BVar' = AVar
            /\ AVar' = AVar

ABSpec_Next == ABSpec_A \/ ABSpec_B

ABSpec_Spec == ABSpec_Init /\ [][ABSpec_Next]_ABSpec_vars

ABSpec_FairSpec == ABSpec_Spec /\ WF_ABSpec_vars(ABSpec_Next)

\* Refinement and liveness property checked of the implementation.
ABSpecProperty == ABSpec_FairSpec

THEOREM FairSpec => [](AB_TypeOK /\ AB_Inv /\ AB_TwoValsSeq)
THEOREM FairSpec => ABSpecProperty
=============================================================================