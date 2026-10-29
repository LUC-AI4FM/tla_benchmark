---------------------------- MODULE AlternatingBit ----------------------------
EXTENDS Integers, Sequences

CONSTANT Data

ASSUME Data # {}

(***************************************************************************)
(* Message records sent from A to B carry data and a control bit.          *)
(* Acknowledgments sent from B to A carry only the bit.                     *)
(***************************************************************************)
Msgs == [data : Data, bit : {0, 1}]

Remove(i, seq) ==
  [j \in 1..(Len(seq) - 1) |-> IF j < i THEN seq[j] ELSE seq[j + 1]]

(***************************************************************************
--algorithm AB {
  variables AVar \in [data : Data, bit : {1}],
            BVar = AVar,
            AtoB = << >>,
            BtoA = << >>;

  macro Send(m, chan) { chan := Append(chan, m) }

  fair process (A = "A") {
    a: while (TRUE) {
         either Send(AVar, AtoB)
         or { await BtoA # << >>;
              if (Head(BtoA) = AVar.bit) {
                with (d \in Data) AVar := [data |-> d, bit |-> 1 - AVar.bit]
              };
              BtoA := Tail(BtoA)
            }
       }
  }

  fair process (B = "B") {
    b: while (TRUE) {
         either Send(BVar.bit, BtoA)
         or { await AtoB # << >>;
              if (Head(AtoB).bit # BVar.bit) { BVar := Head(AtoB) };
              AtoB := Tail(AtoB)
            }
       }
  }

  process (C = "C") {
    c: while (TRUE) {
         either { await AtoB # << >>;
                  with (i \in 1..Len(AtoB)) { AtoB := Remove(i, AtoB) } }
         or     { await BtoA # << >>;
                  with (i \in 1..Len(BtoA)) { BtoA := Remove(i, BtoA) } }
       }
  }
}
***************************************************************************)
\* BEGIN TRANSLATION
VARIABLES AVar, BVar, AtoB, BtoA, pc

vars == << AVar, BVar, AtoB, BtoA, pc >>

ProcSet == {"A"} \cup {"B"} \cup {"C"}

Init == /\ AVar \in [data : Data, bit : {1}]
        /\ BVar = AVar
        /\ AtoB = << >>
        /\ BtoA = << >>
        /\ pc = [self \in ProcSet |-> CASE self = "A" -> "a"
                                        [] self = "B" -> "b"
                                        [] self = "C" -> "c"]

a == /\ pc["A"] = "a"
     /\ \/ /\ AtoB' = Append(AtoB, AVar)
           /\ UNCHANGED << AVar, BtoA >>
        \/ /\ BtoA # << >>
           /\ IF Head(BtoA) = AVar.bit
                 THEN \E d \in Data : AVar' = [data |-> d, bit |-> 1 - AVar.bit]
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

c == /\ pc["C"] = "c"
     /\ \/ /\ AtoB # << >>
           /\ \E i \in 1..Len(AtoB) : AtoB' = Remove(i, AtoB)
           /\ BtoA' = BtoA
        \/ /\ BtoA # << >>
           /\ \E i \in 1..Len(BtoA) : BtoA' = Remove(i, BtoA)
           /\ AtoB' = AtoB
     /\ pc' = [pc EXCEPT !["C"] = "c"]
     /\ UNCHANGED << AVar, BVar >>

C == c

Next == A \/ B \/ C

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(A)
        /\ WF_vars(B)
\* END TRANSLATION

(***************************************************************************)
(* Safety properties                                                        *)
(***************************************************************************)
TypeOK == /\ AVar \in Msgs
          /\ BVar \in Msgs
          /\ AtoB \in Seq(Msgs)
          /\ BtoA \in Seq({0, 1})
          /\ pc \in [ProcSet -> {"a", "b", "c"}]

\* When the bits agree, B holds exactly the message A is currently sending.
Inv == (AVar.bit = BVar.bit) => (AVar = BVar)

(***************************************************************************)
(* Liveness property: every message A holds is eventually delivered to B.  *)
(***************************************************************************)
Delivery == \A v \in Msgs : (AVar = v) ~> (BVar = v)

THEOREM Spec => [](TypeOK /\ Inv)
=============================================================================