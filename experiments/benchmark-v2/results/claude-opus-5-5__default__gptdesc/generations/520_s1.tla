-------------------------------- MODULE AB2 --------------------------------
EXTENDS Integers, Sequences

CONSTANT Data

Remove(i, seq) ==
  [j \in 1..(Len(seq) - 1) |-> IF j < i THEN seq[j] ELSE seq[j + 1]]

(***************************************************************************
--algorithm AB2 {
  variables AVar \in Data \X {0}, BVar = AVar,
            AtoB = << >>, BtoA = << >> ;

  process (A = "A") {
    a: while (TRUE) {
         either { AtoB := Append(AtoB, AVar) }
         or     { await BtoA # << >> ;
                  if (Head(BtoA) = AVar[2]) {
                    with (d \in Data) { AVar := <<d, 1 - AVar[2]>> }
                  } ;
                  BtoA := Tail(BtoA)
                }
       }
  }

  process (B = "B") {
    b: while (TRUE) {
         either { BtoA := Append(BtoA, BVar[2]) }
         or     { await AtoB # << >> ;
                  if (Head(AtoB)[2] # BVar[2]) { BVar := Head(AtoB) } ;
                  AtoB := Tail(AtoB)
                }
       }
  }

  process (LoseMsgs = "L") {
    c: while (TRUE) {
         either with (i \in 1..Len(AtoB)) { AtoB := Remove(i, AtoB) }
         or     with (i \in 1..Len(BtoA)) { BtoA := Remove(i, BtoA) }
       }
  }
}
***************************************************************************)
\* BEGIN TRANSLATION
VARIABLES AVar, BVar, AtoB, BtoA, pc

vars == << AVar, BVar, AtoB, BtoA, pc >>

ProcSet == {"A"} \cup {"B"} \cup {"L"}

Init == /\ AVar \in Data \X {0}
        /\ BVar = AVar
        /\ AtoB = << >>
        /\ BtoA = << >>
        /\ pc = [self \in ProcSet |-> CASE self = "A" -> "a"
                                        [] self = "B" -> "b"
                                        [] self = "L" -> "c"]

a == /\ pc["A"] = "a"
     /\ \/ /\ AtoB' = Append(AtoB, AVar)
           /\ UNCHANGED << AVar, BtoA >>
        \/ /\ BtoA # << >>
           /\ IF Head(BtoA) = AVar[2]
                 THEN \E d \in Data : AVar' = <<d, 1 - AVar[2]>>
                 ELSE AVar' = AVar
           /\ BtoA' = Tail(BtoA)
           /\ AtoB' = AtoB
     /\ pc' = [pc EXCEPT !["A"] = "a"]
     /\ BVar' = BVar

A == a

b == /\ pc["B"] = "b"
     /\ \/ /\ BtoA' = Append(BtoA, BVar[2])
           /\ UNCHANGED << BVar, AtoB >>
        \/ /\ AtoB # << >>
           /\ IF Head(AtoB)[2] # BVar[2]
                 THEN BVar' = Head(AtoB)
                 ELSE BVar' = BVar
           /\ AtoB' = Tail(AtoB)
           /\ BtoA' = BtoA
     /\ pc' = [pc EXCEPT !["B"] = "b"]
     /\ AVar' = AVar

B == b

c == /\ pc["L"] = "c"
     /\ \/ /\ \E i \in 1..Len(AtoB) : AtoB' = Remove(i, AtoB)
           /\ BtoA' = BtoA
        \/ /\ \E i \in 1..Len(BtoA) : BtoA' = Remove(i, BtoA)
           /\ AtoB' = AtoB
     /\ pc' = [pc EXCEPT !["L"] = "c"]
     /\ UNCHANGED << AVar, BVar >>

LoseMsgs == c

Next == A \/ B \/ LoseMsgs

Spec == Init /\ [][Next]_vars
\* END TRANSLATION

-----------------------------------------------------------------------------
TypeOK == /\ AVar \in Data \X {0, 1}
          /\ BVar \in Data \X {0, 1}
          /\ AtoB \in Seq(Data \X {0, 1})
          /\ BtoA \in Seq({0, 1})
          /\ pc \in [ProcSet -> {"a", "b", "c"}]

THEOREM Spec => []TypeOK
=============================================================================