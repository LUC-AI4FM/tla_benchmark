---- MODULE ABRefinementCheck ----
EXTENDS Integers, Sequences

CONSTANT Data

VARIABLES AVar2, BVar2, AtoB, BtoA

vars == <<AVar2, BVar2, AtoB, BtoA>>

ConstData == {"d1", "d2", "d3"}

-----------------------------------------------------------------------------
(* Implementation (Session11c): alternating bit protocol with lossy channels *)

Msgs == Data \X {0, 1}

RemoveAt(seq, i) == [j \in 1..(Len(seq) - 1) |-> IF j < i THEN seq[j] ELSE seq[j + 1]]

Init == /\ AVar2 \in Data \X {1}
        /\ BVar2 = AVar2
        /\ AtoB = << >>
        /\ BtoA = << >>

ASnd == /\ AtoB' = Append(AtoB, AVar2)
        /\ UNCHANGED <<AVar2, BVar2, BtoA>>

ARcv == /\ BtoA # << >>
        /\ IF Head(BtoA) = AVar2[2]
              THEN \E d \in Data : AVar2' = <<d, 1 - AVar2[2]>>
              ELSE AVar2' = AVar2
        /\ BtoA' = Tail(BtoA)
        /\ UNCHANGED <<BVar2, AtoB>>

BSnd == /\ BtoA' = Append(BtoA, BVar2[2])
        /\ UNCHANGED <<AVar2, BVar2, AtoB>>

BRcv == /\ AtoB # << >>
        /\ IF Head(AtoB)[2] # BVar2[2]
              THEN BVar2' = Head(AtoB)
              ELSE BVar2' = BVar2
        /\ AtoB' = Tail(AtoB)
        /\ UNCHANGED <<AVar2, BtoA>>

LoseMsg == \/ /\ \E i \in 1..Len(AtoB) : AtoB' = RemoveAt(AtoB, i)
              /\ UNCHANGED <<AVar2, BVar2, BtoA>>
           \/ /\ \E i \in 1..Len(BtoA) : BtoA' = RemoveAt(BtoA, i)
              /\ UNCHANGED <<AVar2, BVar2, AtoB>>

Next == ASnd \/ ARcv \/ BSnd \/ BRcv \/ LoseMsg

Spec == /\ Init
        /\ [][Next]_vars
        /\ WF_vars(ASnd) /\ WF_vars(BSnd)
        /\ SF_vars(ARcv) /\ SF_vars(BRcv)

-----------------------------------------------------------------------------
(* Model-checking configuration *)

StateConstraint == /\ Len(AtoB) =< 3
                   /\ Len(BtoA) =< 3

AB2_TypeOK == /\ AVar2 \in Msgs
              /\ BVar2 \in Msgs
              /\ AtoB \in Seq(Msgs)
              /\ BtoA \in Seq({0, 1})

-----------------------------------------------------------------------------
(* Refinement mapping to the abstract specification (Session11a)            *)

AVar_Impl == [data |-> AVar2[1], bit |-> AVar2[2]]
BVar_Impl == [data |-> BVar2[1], bit |-> BVar2[2]]

absVars == <<AVar_Impl, BVar_Impl>>

ABS_Init == /\ AVar_Impl \in [data : Data, bit : {1}]
            /\ BVar_Impl = AVar_Impl

ABS_A == /\ AVar_Impl = BVar_Impl
         /\ \E d \in Data : AVar_Impl' = [data |-> d, bit |-> 1 - AVar_Impl.bit]
         /\ BVar_Impl' = BVar_Impl

ABS_B == /\ AVar_Impl # BVar_Impl
         /\ BVar_Impl' = AVar_Impl
         /\ AVar_Impl' = AVar_Impl

ABS_Next == ABS_A \/ ABS_B

ABS_Spec == /\ ABS_Init
            /\ [][ABS_Next]_absVars
            /\ WF_absVars(ABS_A)
            /\ WF_absVars(ABS_B)

ABSpecProperty == ABS_Spec

=============================================================================