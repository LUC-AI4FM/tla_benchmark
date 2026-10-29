------------------------------ MODULE AB ------------------------------
EXTENDS Integers, Sequences

CONSTANT Data

VARIABLES AVar, BVar, AtoB, BtoA

vars == <<AVar, BVar, AtoB, BtoA>>

Msgs == Data \X {0, 1}

TypeOK == /\ AVar \in Msgs
          /\ BVar \in Msgs
          /\ AtoB \in Seq(Msgs)
          /\ BtoA \in Seq({0, 1})

Remove(i, seq) ==
  [j \in 1..(Len(seq) - 1) |-> IF j < i THEN seq[j] ELSE seq[j + 1]]

Init == /\ \E d \in Data : AVar = <<d, 1>>
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

A == ASnd \/ ARcv

B == BSnd \/ BRcv

Next == A \/ B \/ LoseMsg

Spec == Init /\ [][Next]_vars

\* Safety: when sender and receiver agree on the bit, they agree on the data
Inv == /\ TypeOK
       /\ (AVar[2] = BVar[2]) => (AVar = BVar)
       /\ \A i \in 1..Len(AtoB) : AtoB[i][2] = AVar[2] => AtoB[i] = AVar

=============================================================================