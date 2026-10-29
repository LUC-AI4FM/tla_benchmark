------------------------------- MODULE AB2 -------------------------------
EXTENDS Integers, Sequences

CONSTANT Data

Msgs == (Data \X {0, 1}) \cup {0, 1}

Remove(i, seq) ==
  [j \in 1..(Len(seq) - 1) |-> IF j < i THEN seq[j] ELSE seq[j + 1]]

(***************************************************************************
--algorithm AB2 {
  variables AVar2 = <<CHOOSE d \in Data : TRUE, 1>>,
            BVar2 = AVar2,
            AtoB = << >>,
            BtoA = << >> ;

  process (A = "A") {
    a: while (TRUE) {
         either { AtoB := Append(AtoB, AVar2) }
         or     { await BtoA # << >> ;
                  if (Head(BtoA) = AVar2[2]) {
                    with (d \in Data) { AVar2 := <<d, 1 - AVar2[2]>> }
                  } ;
                  BtoA := Tail(BtoA)
                }
       }
  }

  process (B = "B") {
    b: while (TRUE) {
         either { BtoA := Append(BtoA, BVar2[2]) }
         or     { await AtoB # << >> ;
                  if (Head(AtoB)[2] # BVar2[2]) {
                    BVar2 := Head(AtoB)
                  } ;
                  AtoB := Tail(AtoB)
                }
       }
  }

  process (LoseMsgs = "L") {
    c: while (TRUE) {
         either { with (i \in 1..Len(AtoB)) { AtoB := Remove(i, AtoB) } }
         or     { with (i \in 1..Len(BtoA)) { BtoA := Remove(i, BtoA) } }
       }
  }
}
***************************************************************************)
\* BEGIN TRANSLATION
VARIABLES AVar2, BVar2, AtoB, BtoA, pc

vars == << AVar2, BVar2, AtoB, BtoA, pc >>

ProcSet == {"A"} \cup {"B"} \cup {"L"}

Init == /\ AVar2 = <<CHOOSE d \in Data : TRUE, 1>>
        /\ BVar2 = AVar2
        /\ AtoB = << >>
        /\ BtoA = << >>
        /\ pc = [self \in ProcSet |-> CASE self = "A" -> "a"
                                        [] self = "B" -> "b"
                                        [] self = "L" -> "c"]

a == /\ pc["A"] = "a"
     /\ \/ /\ AtoB' = Append(AtoB, AVar2)
           /\ UNCHANGED << AVar2, BtoA >>
        \/ /\ BtoA # << >>
           /\ IF Head(BtoA) = AVar2[2]
                 THEN /\ \E d \in Data : AVar2' = <<d, 1 - AVar2[2]>>
                 ELSE /\ AVar2' = AVar2
           /\ BtoA' = Tail(BtoA)
           /\ AtoB' = AtoB
     /\ pc' = [pc EXCEPT !["A"] = "a"]
     /\ BVar2' = BVar2

A == a

b == /\ pc["B"] = "b"
     /\ \/ /\ BtoA' = Append(BtoA, BVar2[2])
           /\ UNCHANGED << BVar2, AtoB >>
        \/ /\ AtoB # << >>
           /\ IF Head(AtoB)[2] # BVar2[2]
                 THEN /\ BVar2' = Head(AtoB)
                 ELSE /\ BVar2' = BVar2
           /\ AtoB' = Tail(AtoB)
           /\ BtoA' = BtoA
     /\ pc' = [pc EXCEPT !["B"] = "b"]
     /\ AVar2' = AVar2

B == b

c == /\ pc["L"] = "c"
     /\ \/ /\ \E i \in 1..Len(AtoB) : AtoB' = Remove(i, AtoB)
           /\ BtoA' = BtoA
        \/ /\ \E i \in 1..Len(BtoA) : BtoA' = Remove(i, BtoA)
           /\ AtoB' = AtoB
     /\ pc' = [pc EXCEPT !["L"] = "c"]
     /\ UNCHANGED << AVar2, BVar2 >>

LoseMsgs == c

Next == A \/ B \/ LoseMsgs

Spec == Init /\ [][Next]_vars
\* END TRANSLATION

TypeOK == /\ AVar2 \in Data \X {0, 1}
          /\ BVar2 \in Data \X {0, 1}
          /\ AtoB \in Seq(Data \X {0, 1})
          /\ BtoA \in Seq({0, 1})
=============================================================================