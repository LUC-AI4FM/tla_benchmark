-------------------------------- MODULE AB2 --------------------------------
EXTENDS Integers, Sequences

CONSTANT Data

ASSUME Data # {}

RemoveElement(i, seq) ==
    [j \in 1..(Len(seq) - 1) |-> IF j < i THEN seq[j] ELSE seq[j + 1]]

(***************************************************************************
--algorithm AB2 {
    variables AVar = <<CHOOSE d \in Data : TRUE, 1>>,
              BVar = AVar,
              AtoB = << >>,
              BtoA = << >> ;

    process (A = "A") {
      a: while (TRUE) {
           either { AtoB := Append(AtoB, AVar) }
           or     { await BtoA # << >> ;
                    if (Head(BtoA) = AVar[2]) {
                        with (d \in Data) { AVar := <<d, 1 - AVar[2]>> }
                    };
                    BtoA := Tail(BtoA)
                  }
         }
    }

    process (B = "B") {
      b: while (TRUE) {
           either { BtoA := Append(BtoA, BVar[2]) }
           or     { await AtoB # << >> ;
                    if (Head(AtoB)[2] # BVar[2]) { BVar := Head(AtoB) };
                    AtoB := Tail(AtoB)
                  }
         }
    }

    process (LoseMsgs = "L") {
      c: while (TRUE) {
           either with (i \in 1..Len(AtoB)) { AtoB := RemoveElement(i, AtoB) }
           or     with (i \in 1..Len(BtoA)) { BtoA := RemoveElement(i, BtoA) }
         }
    }
}
***************************************************************************)
\* BEGIN TRANSLATION
VARIABLES AVar, BVar, AtoB, BtoA

vars == << AVar, BVar, AtoB, BtoA >>

ProcSet == {"A"} \cup {"B"} \cup {"L"}

Init == (* Global variables *)
        /\ AVar = <<CHOOSE d \in Data : TRUE, 1>>
        /\ BVar = AVar
        /\ AtoB = << >>
        /\ BtoA = << >>

A == /\ \/ /\ AtoB' = Append(AtoB, AVar)
           /\ UNCHANGED << AVar, BtoA >>
        \/ /\ BtoA # << >>
           /\ IF Head(BtoA) = AVar[2]
                 THEN /\ \E d \in Data :
                           AVar' = <<d, 1 - AVar[2]>>
                 ELSE /\ TRUE
                      /\ AVar' = AVar
           /\ BtoA' = Tail(BtoA)
           /\ AtoB' = AtoB
     /\ BVar' = BVar

B == /\ \/ /\ BtoA' = Append(BtoA, BVar[2])
           /\ UNCHANGED << BVar, AtoB >>
        \/ /\ AtoB # << >>
           /\ IF Head(AtoB)[2] # BVar[2]
                 THEN /\ BVar' = Head(AtoB)
                 ELSE /\ TRUE
                      /\ BVar' = BVar
           /\ AtoB' = Tail(AtoB)
           /\ BtoA' = BtoA
     /\ AVar' = AVar

LoseMsgs == /\ \/ /\ \E i \in 1..Len(AtoB) :
                       AtoB' = RemoveElement(i, AtoB)
                  /\ BtoA' = BtoA
               \/ /\ \E i \in 1..Len(BtoA) :
                       BtoA' = RemoveElement(i, BtoA)
                  /\ AtoB' = AtoB
            /\ UNCHANGED << AVar, BVar >>

Next == A \/ B \/ LoseMsgs

Spec == Init /\ [][Next]_vars

\* END TRANSLATION
-----------------------------------------------------------------------------
(* Type-correctness invariant *)
TypeOK == /\ AVar \in Data \X {0, 1}
          /\ BVar \in Data \X {0, 1}
          /\ AtoB \in Seq(Data \X {0, 1})
          /\ BtoA \in Seq({0, 1})
=============================================================================