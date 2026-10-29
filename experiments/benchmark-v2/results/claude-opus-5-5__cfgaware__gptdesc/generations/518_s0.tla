---------------------------- MODULE AlternatingBit ----------------------------
EXTENDS Integers, Sequences

CONSTANT Data

Remove(i, seq) ==
  [j \in 1..(Len(seq) - 1) |-> IF j < i THEN seq[j] ELSE seq[j + 1]]

Msgs == (Data \X {0, 1}) \cup {0, 1}

VARIABLES AVar, BVar, AtoB, BtoA

vars == << AVar, BVar, AtoB, BtoA >>

ProcSet == {"A"} \cup {"B"} \cup {"L"}

Init == /\ AVar \in Data \X {1}
        /\ BVar = AVar
        /\ AtoB = << >>
        /\ BtoA = << >>

A == \/ /\ AtoB' = Append(AtoB, AVar)
        /\ UNCHANGED << AVar, BVar, BtoA >>
     \/ /\ BtoA # << >>
        /\ BtoA' = Tail(BtoA)
        /\ IF Head(BtoA) = AVar[2]
             THEN \E d \in Data : AVar' = << d, 1 - AVar[2] >>
             ELSE AVar' = AVar
        /\ UNCHANGED << BVar, AtoB >>

B == \/ /\ BtoA' = Append(BtoA, BVar[2])
        /\ UNCHANGED << AVar, BVar, AtoB >>
     \/ /\ AtoB # << >>
        /\ AtoB' = Tail(AtoB)
        /\ IF Head(AtoB)[2] # BVar[2]
             THEN BVar' = Head(AtoB)
             ELSE BVar' = BVar
        /\ UNCHANGED << AVar, BtoA >>

LoseMsgs == \/ /\ \E i \in 1..Len(AtoB) : AtoB' = Remove(i, AtoB)
               /\ UNCHANGED << AVar, BVar, BtoA >>
            \/ /\ \E i \in 1..Len(BtoA) : BtoA' = Remove(i, BtoA)
               /\ UNCHANGED << AVar, BVar, AtoB >>

Next == A \/ B \/ LoseMsgs

Spec == Init /\ [][Next]_vars

TypeOK == /\ AVar \in Data \X {0, 1}
          /\ BVar \in Data \X {0, 1}
          /\ AtoB \in Seq(Data \X {0, 1})
          /\ BtoA \in Seq({0, 1})
=============================================================================