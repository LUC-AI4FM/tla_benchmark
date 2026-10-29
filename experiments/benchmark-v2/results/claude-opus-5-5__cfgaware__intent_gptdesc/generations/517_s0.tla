---- MODULE AB ----
(***************************************************************************)
(* Alternating Bit protocol between two participants, A and B.             *)
(* A sends messages <<d, b>> (data, bit) to B over the FIFO channel AtoB.  *)
(* B sends one-bit acknowledgements to A over the FIFO channel BtoA.       *)
(* Both channels are bounded by capacity Cap and may lose messages, which  *)
(* models network nondeterminism.  The intent is to check the safety and   *)
(* liveness properties below with the TLC model checker.                   *)
(***************************************************************************)
EXTENDS Integers, Sequences

CONSTANT Data

VARIABLES AVar, BVar, AtoB, BtoA

vars == << AVar, BVar, AtoB, BtoA >>

\* Data set suitable for substitution for Data in a model.
ConstData == {"d1", "d2"}

\* Channel capacity bound.
Cap == 3

Bits == {0, 1}
Msgs == Data \X Bits

\* Remove the i-th element of sequence s.
Remove(i, s) == [j \in 1..(Len(s) - 1) |-> IF j < i THEN s[j] ELSE s[j + 1]]

---------------------------------------------------------------------------
Init == /\ AVar \in Data \X {1}
        /\ BVar = AVar
        /\ AtoB = << >>
        /\ BtoA = << >>

\* A (re)sends its current message, provided the channel has room.
ASnd == /\ Len(AtoB) < Cap
        /\ AtoB' = Append(AtoB, AVar)
        /\ UNCHANGED << AVar, BVar, BtoA >>

\* A receives an acknowledgement. If it acknowledges the current message,
\* A nondeterministically chooses new data and flips its bit.
ARcv == /\ BtoA # << >>
        /\ IF Head(BtoA) = AVar[2]
             THEN \E d \in Data : AVar' = << d, 1 - AVar[2] >>
             ELSE UNCHANGED AVar
        /\ BtoA' = Tail(BtoA)
        /\ UNCHANGED << BVar, AtoB >>

\* B (re)sends an acknowledgement of the bit of its last received message.
BSnd == /\ Len(BtoA) < Cap
        /\ BtoA' = Append(BtoA, BVar[2])
        /\ UNCHANGED << AVar, BVar, AtoB >>

\* B receives a message; if its bit differs from B's, it is a new message.
BRcv == /\ AtoB # << >>
        /\ IF Head(AtoB)[2] # BVar[2]
             THEN BVar' = Head(AtoB)
             ELSE UNCHANGED BVar
        /\ AtoB' = Tail(AtoB)
        /\ UNCHANGED << AVar, BtoA >>

\* Network nondeterminism: messages may be lost.
LoseMsg == /\ \/ /\ \E i \in 1..Len(AtoB) : AtoB' = Remove(i, AtoB)
                 /\ UNCHANGED BtoA
              \/ /\ \E i \in 1..Len(BtoA) : BtoA' = Remove(i, BtoA)
                 /\ UNCHANGED AtoB
           /\ UNCHANGED << AVar, BVar >>

Next == ASnd \/ ARcv \/ BSnd \/ BRcv \/ LoseMsg

Spec == Init /\ [][Next]_vars

FairSpec == /\ Spec
            /\ WF_vars(ASnd) /\ WF_vars(BSnd)
            /\ SF_vars(ARcv) /\ SF_vars(BRcv)

---------------------------------------------------------------------------
StateConstraint == /\ Len(AtoB) <= Cap
                   /\ Len(BtoA) <= Cap

AB_TypeOK == /\ AVar \in Msgs
             /\ BVar \in Msgs
             /\ AtoB \in Seq(Msgs)
             /\ BtoA \in Seq(Bits)
             /\ Len(AtoB) <= Cap
             /\ Len(BtoA) <= Cap

\* If B's acknowledgement bit equals A's current bit, A and B agree on data.
AB_Inv == (AVar[2] = BVar[2]) => (AVar = BVar)

\* A sequence has at most two consecutive constant blocks.
TwoVals(s) == \A i, j \in 1..(Len(s) - 1) :
                 (s[i] # s[i + 1] /\ s[j] # s[j + 1]) => (i = j)

AB_TwoValsSeq == TwoVals(AtoB) /\ TwoVals(BtoA)

---------------------------------------------------------------------------
\* High-level abstract specification that AB should refine.
ABSInit == /\ AVar \in Data \X {1}
           /\ BVar = AVar

ABSA == /\ AVar = BVar
        /\ \E d \in Data : AVar' = << d, 1 - AVar[2] >>
        /\ UNCHANGED BVar

ABSB == /\ AVar # BVar
        /\ BVar' = AVar
        /\ UNCHANGED AVar

ABSNext == ABSA \/ ABSB

ABSpecProperty == ABSInit /\ [][ABSNext]_<< AVar, BVar >>

\* Liveness goals (to be checked under FairSpec).
ASendsDelivered == []<>(AVar = BVar) /\ []<>(AVar # BVar \/ ENABLED ABSA)
AckPropagates   == (AVar = BVar) ~> (AVar # BVar \/ BtoA = << >>)
ABLiveness      == []<>(AVar = BVar) /\ ((AVar # BVar) ~> (AVar = BVar))
====