------------------------------ MODULE MCSession11b ------------------------------
EXTENDS Integers, Sequences

CONSTANTS Data, MaxLen

ASSUME MaxLen \in Nat

VARIABLES AVar2, BVar2, AtoB, BtoA

vars == <<AVar2, BVar2, AtoB, BtoA>>

Msgs == [data : Data, bit : {0, 1}]

-----------------------------------------------------------------------------
(* Bound the channel lengths for model checking. *)
SeqConstraint == /\ Len(AtoB) =< MaxLen
                 /\ Len(BtoA) =< MaxLen

(* Type-correctness of the refined implementation state. *)
TypeOKImpl == /\ AVar2 \in Data \X {0, 1}
              /\ BVar2 \in Data \X {0, 1}
              /\ AtoB \in Seq(Msgs)
              /\ BtoA \in Seq({0, 1})

-----------------------------------------------------------------------------
(* Implementation-level behavior, where AVar2 and BVar2 are tuples <<data, bit>>. *)
Init == /\ \E d \in Data : AVar2 = <<d, 1>>
        /\ BVar2 = AVar2
        /\ AtoB = << >>
        /\ BtoA = << >>

ASnd == /\ AtoB' = Append(AtoB, [data |-> AVar2[1], bit |-> AVar2[2]])
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
        /\ IF Head(AtoB).bit # BVar2[2]
             THEN BVar2' = <<Head(AtoB).data, Head(AtoB).bit>>
             ELSE BVar2' = BVar2
        /\ AtoB' = Tail(AtoB)
        /\ UNCHANGED <<AVar2, BtoA>>

RemoveElt(i, seq) == [j \in 1..(Len(seq) - 1) |->
                        IF j < i THEN seq[j] ELSE seq[j + 1]]

LoseMsg == /\ \/ /\ \E i \in 1..Len(AtoB) : AtoB' = RemoveElt(i, AtoB)
                 /\ BtoA' = BtoA
              \/ /\ \E i \in 1..Len(BtoA) : BtoA' = RemoveElt(i, BtoA)
                 /\ AtoB' = AtoB
           /\ UNCHANGED <<AVar2, BVar2>>

Next == ASnd \/ ARcv \/ BSnd \/ BRcv \/ LoseMsg

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Refinement mapping: tuples to record-shaped abstract variables. *)
AVar == [data |-> AVar2[1], bit |-> AVar2[2]]
BVar == [data |-> BVar2[1], bit |-> BVar2[2]]

ABSpec == INSTANCE Session11a
            WITH Data <- Data,
                 AVar <- AVar,
                 BVar <- BVar,
                 AtoB <- AtoB,
                 BtoA <- BtoA

(* Property to check: the implementation refines the abstract spec. *)
ABSpecSpec == ABSpec!Spec

THEOREM Spec => []TypeOKImpl
THEOREM Spec => ABSpecSpec
=============================================================================