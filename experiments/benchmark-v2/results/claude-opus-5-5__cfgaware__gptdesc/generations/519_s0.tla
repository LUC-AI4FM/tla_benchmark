------------------------------- MODULE MCAB2 -------------------------------
EXTENDS Integers, Sequences

CONSTANT Data

VARIABLES AVar2, BVar2, AtoB, BtoA

vars == <<AVar2, BVar2, AtoB, BtoA>>

(***************************************************************************)
(* Model value used for Data (bind with  Data <- ConstData).               *)
(***************************************************************************)
ConstData == {"d1", "d2"}

(***************************************************************************)
(* Corrupted messages. A corrupted A->B message is a tuple that is not in  *)
(* Data \X {0,1}. A corrupted B->A message is a value that is not in       *)
(* {0,1}.                                                                  *)
(***************************************************************************)
BadAB == <<"Bad">>
BadBA == 2

GoodAB(m) == m \in Data \X {0,1}
GoodBA(m) == m \in {0,1}

AB2_TypeOK ==
  /\ AVar2 \in Data \X {0,1}
  /\ BVar2 \in Data \X {0,1}
  /\ AtoB \in Seq((Data \X {0,1}) \cup {BadAB})
  /\ BtoA \in Seq({0,1} \cup {BadBA})

Init ==
  /\ AVar2 \in Data \X {1}
  /\ BVar2 = AVar2
  /\ AtoB = << >>
  /\ BtoA = << >>

ASnd ==
  /\ AtoB' = Append(AtoB, AVar2)
  /\ UNCHANGED <<AVar2, BVar2, BtoA>>

ARcv ==
  /\ BtoA # << >>
  /\ IF GoodBA(Head(BtoA)) /\ Head(BtoA) = AVar2[2]
       THEN \E d \in Data : AVar2' = <<d, 1 - AVar2[2]>>
       ELSE AVar2' = AVar2
  /\ BtoA' = Tail(BtoA)
  /\ UNCHANGED <<BVar2, AtoB>>

BSnd ==
  /\ BtoA' = Append(BtoA, BVar2[2])
  /\ UNCHANGED <<AVar2, BVar2, AtoB>>

BRcv ==
  /\ AtoB # << >>
  /\ IF GoodAB(Head(AtoB)) /\ Head(AtoB)[2] # BVar2[2]
       THEN BVar2' = Head(AtoB)
       ELSE BVar2' = BVar2
  /\ AtoB' = Tail(AtoB)
  /\ UNCHANGED <<AVar2, BtoA>>

RemoveIth(s, i) ==
  [j \in 1..(Len(s) - 1) |-> IF j < i THEN s[j] ELSE s[j + 1]]

LoseMsg ==
  /\ \/ /\ \E i \in 1..Len(AtoB) : AtoB' = RemoveIth(AtoB, i)
        /\ BtoA' = BtoA
     \/ /\ \E i \in 1..Len(BtoA) : BtoA' = RemoveIth(BtoA, i)
        /\ AtoB' = AtoB
  /\ UNCHANGED <<AVar2, BVar2>>

CorruptMsg ==
  /\ \/ /\ \E i \in 1..Len(AtoB) : AtoB' = [AtoB EXCEPT ![i] = BadAB]
        /\ BtoA' = BtoA
     \/ /\ \E i \in 1..Len(BtoA) : BtoA' = [BtoA EXCEPT ![i] = BadBA]
        /\ AtoB' = AtoB
  /\ UNCHANGED <<AVar2, BVar2>>

Next == ASnd \/ ARcv \/ BSnd \/ BRcv \/ LoseMsg \/ CorruptMsg

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------

StateConstraint ==
  /\ Len(AtoB) <= 3
  /\ Len(BtoA) <= 3

AVarMap == [data |-> AVar2[1], bit |-> AVar2[2]]
BVarMap == [data |-> BVar2[1], bit |-> BVar2[2]]

ABSpec == INSTANCE Session11a WITH AVar <- AVarMap, BVar <- BVarMap

ABSpecProperty == ABSpec!Spec
=============================================================================