---------------------------- MODULE PCalAlternatingBit ----------------------------
EXTENDS Integers, Sequences

CONSTANT Data

Msgs == [data : Data, bit : {0, 1}]

Remove(i, seq) == [j \in 1..(Len(seq) - 1) |-> IF j < i THEN seq[j] ELSE seq[j + 1]]

(***************************************************************************
--algorithm ABProtocol {
  variables AVar \in [data : Data, bit : {1}],
            BVar = AVar,
            AtoB = << >>,
            BtoA = << >> ;

  fair process (A = "A") {
    a: while (TRUE) {
         either AtoB := Append(AtoB, AVar)
         or { await BtoA # << >> ;
              if (Head(BtoA) = AVar.bit) {
                with (d \in Data) { AVar := [data |-> d, bit |-> 1 - AVar.bit] }
              } ;
              BtoA := Tail(BtoA)
            }
       }
  }

  fair process (B = "B") {
    b: while (TRUE) {
         either BtoA := Append(BtoA, BVar.bit)
         or { await AtoB # << >> ;
              if (Head(AtoB).bit # BVar.bit) { BVar := Head(AtoB) } ;
              AtoB := Tail(AtoB)
            }
       }
  }

  process (LoseMsg = "L") {
    c: while (TRUE) {
         either with (i \in 1..Len(AtoB)) { AtoB := Remove(i, AtoB) }
         or     with (i \in 1..Len(BtoA)) { BtoA := Remove(i, BtoA) }
       }
  }
}
***************************************************************************)
\* BEGIN TRANSLATION
VARIABLES AVar, BVar, AtoB, BtoA

vars == << AVar, BVar, AtoB, BtoA >>

ProcSet == {"A"} \cup {"B"} \cup {"L"}

Init == /\ AVar \in [data : Data, bit : {1}]
        /\ BVar = AVar
        /\ AtoB = << >>
        /\ BtoA = << >>

A == \/ /\ AtoB' = Append(AtoB, AVar)
        /\ UNCHANGED << AVar, BVar, BtoA >>
     \/ /\ BtoA # << >>
        /\ IF Head(BtoA) = AVar.bit
              THEN /\ \E d \in Data : AVar' = [data |-> d, bit |-> 1 - AVar.bit]
              ELSE /\ AVar' = AVar
        /\ BtoA' = Tail(BtoA)
        /\ UNCHANGED << BVar, AtoB >>

B == \/ /\ BtoA' = Append(BtoA, BVar.bit)
        /\ UNCHANGED << AVar, BVar, AtoB >>
     \/ /\ AtoB # << >>
        /\ IF Head(AtoB).bit # BVar.bit
              THEN /\ BVar' = Head(AtoB)
              ELSE /\ BVar' = BVar
        /\ AtoB' = Tail(AtoB)
        /\ UNCHANGED << AVar, BtoA >>

LoseMsg == \/ /\ \E i \in 1..Len(AtoB) : AtoB' = Remove(i, AtoB)
              /\ UNCHANGED << AVar, BVar, BtoA >>
           \/ /\ \E i \in 1..Len(BtoA) : BtoA' = Remove(i, BtoA)
              /\ UNCHANGED << AVar, BVar, AtoB >>

Next == A \/ B \/ LoseMsg

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(A)
        /\ WF_vars(B)
\* END TRANSLATION

TypeOK == /\ AVar \in Msgs
          /\ BVar \in Msgs
          /\ AtoB \in Seq(Msgs)
          /\ BtoA \in Seq({0, 1})
==================================================================================