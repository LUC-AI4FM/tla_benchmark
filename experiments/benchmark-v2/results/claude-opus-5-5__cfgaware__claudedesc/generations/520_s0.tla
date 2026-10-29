---------------------------- MODULE AB2 ----------------------------
EXTENDS Naturals, Sequences

CONSTANT Data

Msgs == Data \X {0, 1}

VARIABLES AVar2, BVar2, AtoB, BtoA

vars == << AVar2, BVar2, AtoB, BtoA >>

Remove(i, seq) == [j \in 1..(Len(seq) - 1) |-> IF j < i THEN seq[j] ELSE seq[j + 1]]

TypeOK == /\ AVar2 \in Msgs
          /\ BVar2 \in Msgs
          /\ AtoB \in Seq(Msgs)
          /\ BtoA \in Seq({0, 1})

Init == /\ AVar2 \in Data \X {1}
        /\ BVar2 = AVar2
        /\ AtoB = << >>
        /\ BtoA = << >>

A == \/ /\ AtoB' = Append(AtoB, AVar2)
        /\ UNCHANGED << AVar2, BVar2, BtoA >>
     \/ /\ BtoA # << >>
        /\ IF Head(BtoA) = AVar2[2]
             THEN \E d \in Data : AVar2' = << d, 1 - AVar2[2] >>
             ELSE AVar2' = AVar2
        /\ BtoA' = Tail(BtoA)
        /\ UNCHANGED << BVar2, AtoB >>

B == \/ /\ BtoA' = Append(BtoA, BVar2[2])
        /\ UNCHANGED << AVar2, BVar2, AtoB >>
     \/ /\ AtoB # << >>
        /\ IF Head(AtoB)[2] # BVar2[2]
             THEN BVar2' = Head(AtoB)
             ELSE BVar2' = BVar2
        /\ AtoB' = Tail(AtoB)
        /\ UNCHANGED << AVar2, BtoA >>

LoseMsgs == /\ \/ /\ \E i \in 1..Len(AtoB) : AtoB' = Remove(i, AtoB)
                  /\ BtoA' = BtoA
               \/ /\ \E i \in 1..Len(BtoA) : BtoA' = Remove(i, BtoA)
                  /\ AtoB' = AtoB
            /\ UNCHANGED << AVar2, BVar2 >>

Next == A \/ B \/ LoseMsgs

Spec == Init /\ [][Next]_vars

=============================================================================