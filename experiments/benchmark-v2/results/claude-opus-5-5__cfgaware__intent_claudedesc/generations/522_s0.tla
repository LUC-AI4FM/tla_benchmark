------------------------------- MODULE ABSpec -------------------------------
EXTENDS Integers, Sequences

CONSTANT Data

VARIABLES AVar, BVar, AtoB, BtoA

vars == <<AVar, BVar, AtoB, BtoA>>

Msgs == Data \X {0, 1}

Remove(i, s) ==
  [j \in 1..(Len(s) - 1) |-> IF j < i THEN s[j] ELSE s[j + 1]]

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
  /\ UNCHANGED <<AVar, BtoA, BVar>>

ARcv ==
  /\ BtoA /= << >>
  /\ IF Head(BtoA) = AVar[2]
       THEN \E d \in Data : AVar' = <<d, 1 - AVar[2]>>
       ELSE AVar' = AVar
  /\ BtoA' = Tail(BtoA)
  /\ UNCHANGED <<AtoB, BVar>>

BSnd ==
  /\ BtoA' = Append(BtoA, BVar[2])
  /\ UNCHANGED <<AVar, BVar, AtoB>>

BRcv ==
  /\ AtoB /= << >>
  /\ IF Head(AtoB)[2] /= BVar[2]
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
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(ASnd)
  /\ WF_vars(BSnd)
  /\ SF_vars(ARcv)
  /\ SF_vars(BRcv)

Inv == (AVar[2] = BVar[2]) => (AVar = BVar)

ABPInv == TypeOK /\ Inv

Progress == \A v \in Msgs : (AVar = v) ~> (BVar = v)

=============================================================================