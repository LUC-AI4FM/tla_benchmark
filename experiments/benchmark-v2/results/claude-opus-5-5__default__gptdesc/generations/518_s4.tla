---------------------------- MODULE AlternatingBit ----------------------------
EXTENDS Integers, Sequences

CONSTANT Data

RemoveElt(i, seq) == [j \in 1..(Len(seq)-1) |-> IF j < i THEN seq[j]
                                                          ELSE seq[j+1]]

(***************************************************************************
--algorithm ABProtocol {
  variables AVar \in Data \X {1}, BVar = AVar, AtoB = << >>, BtoA = << >> ;

  process (A = "A") {
    a: while (TRUE) {
         either AtoB := Append(AtoB, AVar)
         or { await BtoA # << >> ;
              if (Head(BtoA) = AVar[2])
                { with (d \in Data) { AVar := <<d, 1 - AVar[2]>> } } ;
              BtoA := Tail(BtoA) }
       }
  }

  process (B = "B") {
    b: while (TRUE) {
         either BtoA := Append(BtoA, BVar[2])
         or { await AtoB # << >> ;
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
        /\ UNCHANGED << AVar, BtoA >>
     \/ /\ BtoA # << >>
        /\ IF Head(BtoA) = AVar[2]
              THEN /\ \E d \in Data : AVar' = <<d, 1 - AVar[2]>>
              ELSE /\ AVar' = AVar
        /\ BtoA' = Tail(BtoA)
        /\ AtoB' = AtoB
     \* BVar unchanged in both branches
A_ == A /\ BVar' = BVar

B == \/ /\ BtoA' = Append(BtoA, BVar[2])
        /\ UNCHANGED << BVar, AtoB >>
     \/ /\ AtoB # << >>
        /\ IF Head(AtoB)[2] # BVar[2]
              THEN /\ BVar' = Head(AtoB)
              ELSE /\ BVar' = BVar
        /\ AtoB' = Tail(AtoB)
        /\ BtoA' = BtoA
B_ == B /\ AVar' = AVar

LoseMsgs == /\ \/ /\ \E i \in 1..Len(AtoB) : AtoB' = RemoveElt(i, AtoB)
                  /\ BtoA' = BtoA
               \/ /\ \E i \in 1..Len(BtoA) : BtoA' = RemoveElt(i, BtoA)
                  /\ AtoB' = AtoB
            /\ UNCHANGED << AVar, BVar >>

Next == A_ \/ B_ \/ LoseMsgs

Spec == Init /\ [][Next]_vars
\* END TRANSLATION

-----------------------------------------------------------------------------
Messages == (Data \X {0, 1}) \cup {0, 1}

TypeOK == /\ AVar \in Data \X {0, 1}
          /\ BVar \in Data \X {0, 1}
          /\ AtoB \in Seq(Data \X {0, 1})
          /\ BtoA \in Seq({0, 1})

(* When A's and B's bits agree, B holds exactly the value A is sending. *)
Inv == (AVar[2] = BVar[2]) => (AVar = BVar)

THEOREM Spec => [](TypeOK /\ Inv)
=============================================================================