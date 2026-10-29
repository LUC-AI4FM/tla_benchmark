---------------------------- MODULE ABProtocol ----------------------------
EXTENDS Integers, Sequences

CONSTANT Data

Remove(i, seq) ==
  [j \in 1..(Len(seq) - 1) |-> IF j < i THEN seq[j] ELSE seq[j + 1]]

Msgs == [data : Data, bit : {0, 1}]

(***************************************************************************
--algorithm ABProtocol {
  variables AVar \in Msgs, BVar = AVar,
            AtoB = << >>, BtoA = << >>;

  fair process (A = "A") {
    a: while (TRUE) {
         either AtoB := Append(AtoB, AVar)
         or { await BtoA # << >>;
              if (Head(BtoA) = AVar.bit) {
                with (d \in Data) { AVar := [data |-> d, bit |-> 1 - AVar.bit] }
              };
              BtoA := Tail(BtoA) }
       }
  }

  fair process (B = "B") {
    b: while (TRUE) {
         either BtoA := Append(BtoA, BVar.bit)
         or { await AtoB # << >>;
              if (Head(AtoB).bit # BVar.bit) { BVar := Head(AtoB) };
              AtoB := Tail(AtoB) }
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
VARIABLES AVar, BVar, AtoB, BtoA, pc

vars == << AVar, BVar, AtoB, BtoA, pc >>

ProcSet == {"A"} \cup {"B"} \cup {"L"}

Init == /\ AVar \in Msgs
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
           /\ IF Head(BtoA) = AVar.bit
                 THEN \E d \in Data :
                        AVar' = [data |-> d, bit |-> 1 - AVar.bit]
                 ELSE AVar' = AVar
           /\ BtoA' = Tail(BtoA)
           /\ AtoB' = AtoB
     /\ pc' = [pc EXCEPT !["A"] = "a"]
     /\ BVar' = BVar

A == a

b == /\ pc["B"] = "b"
     /\ \/ /\ BtoA' = Append(BtoA, BVar.bit)
           /\ UNCHANGED << BVar, AtoB >>
        \/ /\ AtoB # << >>
           /\ IF Head(AtoB).bit # BVar.bit
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

LoseMsg == c

Next == A \/ B \/ LoseMsg

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(A)
        /\ WF_vars(B)
\* END TRANSLATION

-----------------------------------------------------------------------------
TypeOK == /\ AVar \in Msgs
          /\ BVar \in Msgs
          /\ AtoB \in Seq(Msgs)
          /\ BtoA \in Seq({0, 1})
          /\ pc \in [ProcSet -> {"a", "b", "c"}]

Inv == (AVar.bit = BVar.bit) => (AVar = BVar)

THEOREM Spec => [](TypeOK /\ Inv)
=============================================================================