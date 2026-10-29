---- MODULE AlternatingBit ----
EXTENDS Integers, Sequences

CONSTANT Data

VARIABLES AVar, BVar, AtoB, BtoA

vars == <<AVar, BVar, AtoB, BtoA>>

Msgs == Data \X {0, 1}

-----------------------------------------------------------------------------
Remove(i, s) == [j \in 1..(Len(s) - 1) |-> IF j < i THEN s[j] ELSE s[j + 1]]

TypeOK ==
  /\ AVar \in Msgs
  /\ BVar \in Msgs
  /\ AtoB \in Seq(Msgs)
  /\ BtoA \in Seq({0, 1})

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
  /\ BtoA' = Tail(BtoA)
  /\ IF Head(BtoA) = AVar[2]
       THEN \E d \in Data : AVar' = <<d, 1 - AVar[2]>>
       ELSE AVar' = AVar
  /\ UNCHANGED <<BVar, AtoB>>

BSnd ==
  /\ BtoA' = Append(BtoA, BVar[2])
  /\ UNCHANGED <<AVar, BVar, AtoB>>

BRcv ==
  /\ AtoB # << >>
  /\ AtoB' = Tail(AtoB)
  /\ IF Head(AtoB)[2] # BVar[2]
       THEN BVar' = Head(AtoB)
       ELSE BVar' = BVar
  /\ UNCHANGED <<AVar, BtoA>>

A == ASnd \/ ARcv

B == BSnd \/ BRcv

LoseMsg ==
  /\ \/ /\ \E i \in 1..Len(AtoB) : AtoB' = Remove(i, AtoB)
        /\ BtoA' = BtoA
     \/ /\ \E i \in 1..Len(BtoA) : BtoA' = Remove(i, BtoA)
        /\ AtoB' = AtoB
  /\ UNCHANGED <<AVar, BVar>>

Next == A \/ B \/ LoseMsg

Spec == Init /\ [][Next]_vars

FairSpec == Spec /\ WF_vars(ASnd) /\ WF_vars(BSnd) /\ SF_vars(ARcv) /\ SF_vars(BRcv)

-----------------------------------------------------------------------------
(* Safety properties *)

\* When bits agree, B holds exactly A's current item; otherwise A is one ahead.
Inv ==
  /\ TypeOK
  /\ (AVar[2] = BVar[2]) => (AVar = BVar)
  /\ \A i \in 1..Len(AtoB) : AtoB[i] \in {AVar, BVar}
  /\ \A i \in 1..Len(BtoA) : BtoA[i] \in {AVar[2], BVar[2]}
  \* FIFO ordering: messages carrying the old value precede those carrying the new
  /\ \A i, j \in 1..Len(AtoB) :
       (i < j /\ AtoB[i] = AVar /\ AVar # BVar) => AtoB[j] = AVar
  /\ \A i, j \in 1..Len(BtoA) :
       (i < j /\ BtoA[i] = AVar[2]) => BtoA[j] = AVar[2]

\* No corruption: every message in transit carries a payload/bit pair that the
\* sender actually holds or held.
NoCorruption ==
  /\ \A i \in 1..Len(AtoB) : AtoB[i] \in {AVar, BVar}
  /\ \A i \in 1..Len(BtoA) : BtoA[i] \in {AVar[2], BVar[2]}

\* Receiver delivers a new item only if it is the sender's current item with
\* the matching bit (no duplicates, in order).
DeliverOK ==
  [][(BVar' # BVar) => (BVar' = AVar /\ BVar'[2] # BVar[2])]_vars

\* Sender advances only after the current item was acknowledged/delivered.
AdvanceOK ==
  [][(AVar' # AVar) => (AVar = BVar /\ AVar'[2] = 1 - AVar[2])]_vars

\* Liveness (under FairSpec)
SenderProgress == \A b \in {0, 1} : (AVar[2] = b) ~> (AVar[2] # b)
ReceiverProgress == (AVar # BVar) ~> (AVar = BVar)

=============================================================================