--------------------------------- MODULE AB2 ---------------------------------
EXTENDS Integers, Sequences

CONSTANT Data

RemoveElt(i, seq) ==
  [j \in 1..(Len(seq) - 1) |-> IF j < i THEN seq[j] ELSE seq[j + 1]]

Msgs == Data \X {0, 1}

(***************************************************************************
--algorithm AB2 {
  variables AVar \in Data \X {1}, BVar = AVar,
            AtoB = << >>, BtoA = << >> ;

  process (A = "A") {
   a: while (TRUE) {
        either { AtoB := Append(AtoB, AVar) }
        or     { await BtoA # << >> ;
                 if (Head(BtoA) = AVar[2])
                   { with (d \in Data) { AVar := <<d, 1 - AVar[2]>> } } ;
                 BtoA := Tail(BtoA) }
      }
  }

  process (B = "B") {
   b: while (TRUE) {
        either { BtoA := Append(BtoA, BVar[2]) }
        or     { await AtoB # << >> ;
                 if (Head(AtoB)[2] # BVar[2]) { BVar := Head(AtoB) } ;
                 AtoB := Tail(AtoB) }
      }
  }

  process (LoseMsgs = "L") {
   c: while (TRUE) {
        either with (i \in 1..Len(AtoB)) { AtoB := RemoveElt(i, AtoB) }
        or     with (i \in 1..Len(BtoA)) { BtoA := RemoveElt(i, BtoA) }
      }
  }
}
***************************************************************************)
\* BEGIN TRANSLATION
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
        /\ IF Head(BtoA) = AVar[2]
              THEN /\ \E d \in Data : AVar' = <<d, 1 - AVar[2]>>
              ELSE /\ AVar' = AVar
        /\ BtoA' = Tail(BtoA)
        /\ UNCHANGED << BVar, AtoB >>

B == \/ /\ BtoA' = Append(BtoA, BVar[2])
        /\ UNCHANGED << AVar, BVar, AtoB >>
     \/ /\ AtoB # << >>
        /\ IF Head(AtoB)[2] # BVar[2]
              THEN /\ BVar' = Head(AtoB)
              ELSE /\ BVar' = BVar
        /\ AtoB' = Tail(AtoB)
        /\ UNCHANGED << AVar, BtoA >>

LoseMsgs == \/ /\ \E i \in 1..Len(AtoB) : AtoB' = RemoveElt(i, AtoB)
                /\ UNCHANGED << AVar, BVar, BtoA >>
            \/ /\ \E i \in 1..Len(BtoA) : BtoA' = RemoveElt(i, BtoA)
                /\ UNCHANGED << AVar, BVar, AtoB >>

Next == A \/ B \/ LoseMsgs

Spec == Init /\ [][Next]_vars
\* END TRANSLATION

-----------------------------------------------------------------------------
TypeOK == /\ AVar \in Msgs
          /\ BVar \in Msgs
          /\ AtoB \in Seq(Msgs)
          /\ BtoA \in Seq({0, 1})

Inv == (AVar[2] = BVar[2]) => (AVar = BVar)
=============================================================================