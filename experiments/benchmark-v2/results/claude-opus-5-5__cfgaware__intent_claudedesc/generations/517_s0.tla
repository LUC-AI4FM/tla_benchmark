------------------------------- MODULE AB -------------------------------
EXTENDS Integers, Sequences

CONSTANT Data

VARIABLES AVar, BVar, AtoB, BtoA

vars == << AVar, BVar, AtoB, BtoA >>

Bits == {0, 1}

-----------------------------------------------------------------------------
(* Model value used to instantiate the Data constant. *)
ConstData == {"Alice", "Bob"}

(* Bound on channel lengths for model checking. *)
StateConstraint == /\ Len(AtoB) =< 3
                   /\ Len(BtoA) =< 3

-----------------------------------------------------------------------------
AB_TypeOK == /\ AVar \in Data \X Bits
             /\ BVar \in Data \X Bits
             /\ AtoB \in Seq(Data \X Bits)
             /\ BtoA \in Seq(Bits)

Init == /\ AVar \in Data \X {1}
        /\ BVar = AVar
        /\ AtoB = << >>
        /\ BtoA = << >>

(* Sender sends (or resends) its current message. *)
ASnd == /\ AtoB' = Append(AtoB, AVar)
        /\ UNCHANGED << AVar, BVar, BtoA >>

(* Sender receives an acknowledgment bit. *)
ARcv == /\ BtoA # << >>
        /\ IF Head(BtoA) = AVar[2]
             THEN \E d \in Data : AVar' = << d, 1 - AVar[2] >>
             ELSE AVar' = AVar
        /\ BtoA' = Tail(BtoA)
        /\ UNCHANGED << BVar, AtoB >>

(* Receiver sends (or resends) an acknowledgment of its current bit. *)
BSnd == /\ BtoA' = Append(BtoA, BVar[2])
        /\ UNCHANGED << AVar, BVar, AtoB >>

(* Receiver receives a message. *)
BRcv == /\ AtoB # << >>
        /\ IF Head(AtoB)[2] # BVar[2]
             THEN BVar' = Head(AtoB)
             ELSE BVar' = BVar
        /\ AtoB' = Tail(AtoB)
        /\ UNCHANGED << AVar, BtoA >>

RemoveElement(i, seq) ==
    [j \in 1..(Len(seq) - 1) |-> IF j < i THEN seq[j] ELSE seq[j + 1]]

(* A channel may lose any message in transit. *)
LoseMsg == /\ \/ /\ \E i \in 1..Len(AtoB) : AtoB' = RemoveElement(i, AtoB)
                 /\ BtoA' = BtoA
              \/ /\ \E i \in 1..Len(BtoA) : BtoA' = RemoveElement(i, BtoA)
                 /\ AtoB' = AtoB
           /\ UNCHANGED << AVar, BVar >>

Next == ASnd \/ ARcv \/ BSnd \/ BRcv \/ LoseMsg

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* A sequence consisting of at most two contiguous blocks of values. *)
IsTwoValSeq(s) ==
    \E i \in 0..Len(s) :
        /\ \A j \in 1..i : s[j] = s[1]
        /\ \A j \in (i + 1)..Len(s) : s[j] = s[Len(s)]

AB_TwoValsSeq == /\ IsTwoValSeq(AtoB)
                 /\ IsTwoValSeq(BtoA)

AB_Inv == /\ AB_TypeOK
          /\ (\E i \in 1..Len(BtoA) : BtoA[i] = AVar[2]) => (BVar = AVar)
          /\ (AVar[2] = BVar[2]) => (AVar = BVar)
          /\ \A i \in 1..Len(AtoB) : AtoB[i][2] = AVar[2] => AtoB[i] = AVar
          /\ AB_TwoValsSeq

-----------------------------------------------------------------------------
(* High-level alternating bit specification (ABSpec), over the same       *)
(* variables AVar and BVar, used as a refinement property.                *)

ABS_Init == /\ AVar \in Data \X {1}
            /\ BVar = AVar

ABS_A == /\ AVar = BVar
         /\ \E d \in Data : AVar' = << d, 1 - AVar[2] >>
         /\ BVar' = BVar

ABS_B == /\ AVar # BVar
         /\ BVar' = AVar
         /\ AVar' = AVar

ABS_Next == ABS_A \/ ABS_B

ABS_Spec == ABS_Init /\ [][ABS_Next]_<< AVar, BVar >>

ABSpecProperty == ABS_Spec

=============================================================================