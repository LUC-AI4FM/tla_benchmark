------------------------------ MODULE AB ------------------------------
EXTENDS Integers, Sequences

CONSTANT Data

VARIABLES AVar2, BVar2, AtoB, BtoA

vars == << AVar2, BVar2, AtoB, BtoA >>

Bits == {0, 1}

Msgs == Data \X Bits

-----------------------------------------------------------------------------

TypeOK ==
    /\ AVar2 \in Msgs
    /\ BVar2 \in Msgs
    /\ AtoB \in Seq(Msgs)
    /\ BtoA \in Seq(Bits)

Init ==
    /\ AVar2 \in Data \X {1}
    /\ BVar2 = AVar2
    /\ AtoB = << >>
    /\ BtoA = << >>

-----------------------------------------------------------------------------

ASnd ==
    /\ AtoB' = Append(AtoB, AVar2)
    /\ UNCHANGED << AVar2, BVar2, BtoA >>

ARcv ==
    /\ BtoA # << >>
    /\ IF Head(BtoA) = AVar2[2]
         THEN \E d \in Data : AVar2' = << d, 1 - AVar2[2] >>
         ELSE AVar2' = AVar2
    /\ BtoA' = Tail(BtoA)
    /\ UNCHANGED << BVar2, AtoB >>

BSnd ==
    /\ BtoA' = Append(BtoA, BVar2[2])
    /\ UNCHANGED << AVar2, BVar2, AtoB >>

BRcv ==
    /\ AtoB # << >>
    /\ IF Head(AtoB)[2] # BVar2[2]
         THEN BVar2' = Head(AtoB)
         ELSE BVar2' = BVar2
    /\ AtoB' = Tail(AtoB)
    /\ UNCHANGED << AVar2, BtoA >>

RemoveElt(i, seq) ==
    [j \in 1..(Len(seq) - 1) |-> IF j < i THEN seq[j] ELSE seq[j + 1]]

LoseMsgAtoB ==
    /\ \E i \in 1..Len(AtoB) : AtoB' = RemoveElt(i, AtoB)
    /\ UNCHANGED << AVar2, BVar2, BtoA >>

LoseMsgBtoA ==
    /\ \E i \in 1..Len(BtoA) : BtoA' = RemoveElt(i, BtoA)
    /\ UNCHANGED << AVar2, BVar2, AtoB >>

LoseMsg == LoseMsgAtoB \/ LoseMsgBtoA

Next == ASnd \/ ARcv \/ BSnd \/ BRcv \/ LoseMsg

Spec == Init /\ [][Next]_vars

FairSpec ==
    /\ Spec
    /\ SF_vars(ARcv) /\ SF_vars(BRcv)
    /\ WF_vars(ASnd) /\ WF_vars(BSnd)

-----------------------------------------------------------------------------

(* Safety / agreement: the receiver's value either equals the sender's
   current value, or (when bits differ) the sender has moved on after the
   receiver accepted its previous value. Data in channels is consistent. *)
Inv ==
    /\ TypeOK
    /\ \/ BVar2 = AVar2
       \/ BVar2[2] # AVar2[2]
    /\ \A i \in 1..Len(AtoB) :
          AtoB[i][2] = AVar2[2] => AtoB[i] = AVar2

(* Refinement to a higher-level reliable transfer spec *)
ABSpecInit ==
    /\ AVar2 \in Data \X {1}
    /\ BVar2 = AVar2

ABSpecA ==
    /\ AVar2 = BVar2
    /\ \E d \in Data : AVar2' = << d, 1 - AVar2[2] >>
    /\ BVar2' = BVar2

ABSpecB ==
    /\ AVar2 # BVar2
    /\ BVar2' = AVar2
    /\ AVar2' = AVar2

ABSpec == ABSpecInit /\ [][ABSpecA \/ ABSpecB]_<< AVar2, BVar2 >>

=============================================================================