------------------------------ MODULE ABProtocol ------------------------------
EXTENDS Integers, Sequences

CONSTANT Data

Remove(i, seq) ==
  [j \in 1..(Len(seq) - 1) |-> IF j < i THEN seq[j] ELSE seq[j + 1]]

Msgs == [data : Data, bit : {0, 1}]

(***************************************************************************
--algorithm ABAlgorithm {
  variables AVar = [data |-> CHOOSE d \in Data : TRUE, bit |-> 1],
            BVar = AVar,
            AtoB = << >>,
            BtoA = << >>;

  macro Send(m, chan) { chan := Append(chan, m) }
  macro Rcv(v, chan)  { await chan # << >>;
                        v := Head(chan);
                        chan := Tail(chan) }

  fair process (A = "A")
    variable msgA = 0;
  { a: while (TRUE) {
         either Send(AVar, AtoB)
         or     { Rcv(msgA, BtoA);
                  if (msgA = AVar.bit)
                    { with (d \in Data)
                        AVar := [data |-> d, bit |-> 1 - AVar.bit] }
                }
       }
  }

  fair process (B = "B")
    variable msgB = [data |-> CHOOSE d \in Data : TRUE, bit |-> 1];
  { b: while (TRUE) {
         either Send(BVar.bit, BtoA)
         or     { Rcv(msgB, AtoB);
                  if (msgB.bit # BVar.bit) { BVar := msgB }
                }
       }
  }

  process (LoseMsg = "L")
  { c: while (TRUE) {
         either with (i \in 1..Len(AtoB)) { AtoB := Remove(i, AtoB) }
         or     with (i \in 1..Len(BtoA)) { BtoA := Remove(i, BtoA) }
       }
  }
}
***************************************************************************)
\* BEGIN TRANSLATION
VARIABLES AVar, BVar, AtoB, BtoA, pc, msgA, msgB

vars == << AVar, BVar, AtoB, BtoA, pc, msgA, msgB >>

ProcSet == {"A"} \cup {"B"} \cup {"L"}

Init == /\ AVar = [data |-> CHOOSE d \in Data : TRUE, bit |-> 1]
        /\ BVar = AVar
        /\ AtoB = << >>
        /\ BtoA = << >>
        /\ msgA = 0
        /\ msgB = [data |-> CHOOSE d \in Data : TRUE, bit |-> 1]
        /\ pc = [self \in ProcSet |-> CASE self = "A" -> "a"
                                        [] self = "B" -> "b"
                                        [] self = "L" -> "c"]

a == /\ pc["A"] = "a"
     /\ \/ /\ AtoB' = Append(AtoB, AVar)
           /\ UNCHANGED << AVar, BtoA, msgA >>
        \/ /\ BtoA # << >>
           /\ msgA' = Head(BtoA)
           /\ BtoA' = Tail(BtoA)
           /\ IF msgA' = AVar.bit
                 THEN /\ \E d \in Data :
                           AVar' = [data |-> d, bit |-> 1 - AVar.bit]
                 ELSE /\ UNCHANGED AVar
           /\ UNCHANGED AtoB
     /\ pc' = [pc EXCEPT !["A"] = "a"]
     /\ UNCHANGED << BVar, msgB >>

A == a

b == /\ pc["B"] = "b"
     /\ \/ /\ BtoA' = Append(BtoA, BVar.bit)
           /\ UNCHANGED << BVar, AtoB, msgB >>
        \/ /\ AtoB # << >>
           /\ msgB' = Head(AtoB)
           /\ AtoB' = Tail(AtoB)
           /\ IF msgB'.bit # BVar.bit
                 THEN /\ BVar' = msgB'
                 ELSE /\ UNCHANGED BVar
           /\ UNCHANGED BtoA
     /\ pc' = [pc EXCEPT !["B"] = "b"]
     /\ UNCHANGED << AVar, msgA >>

B == b

c == /\ pc["L"] = "c"
     /\ \/ /\ \E i \in 1..Len(AtoB) :
                 AtoB' = Remove(i, AtoB)
           /\ UNCHANGED BtoA
        \/ /\ \E i \in 1..Len(BtoA) :
                 BtoA' = Remove(i, BtoA)
           /\ UNCHANGED AtoB
     /\ pc' = [pc EXCEPT !["L"] = "c"]
     /\ UNCHANGED << AVar, BVar, msgA, msgB >>

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
          /\ msgA \in {0, 1}
          /\ msgB \in Msgs
          /\ pc \in [ProcSet -> {"a", "b", "c"}]

\* When B's bit matches A's bit, B holds exactly A's current message.
Inv == (AVar.bit = BVar.bit) => (AVar = BVar)

THEOREM Spec => [](TypeOK /\ Inv)
=============================================================================