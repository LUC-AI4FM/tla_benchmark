------------------------------- MODULE ABAlg -------------------------------
(***************************************************************************)
(* The Alternating Bit protocol, omitting liveness requirements.           *)
(* A sender process A, a receiver process B, and a message-loss process    *)
(* LoseMsgs communicate over the FIFO channels AtoB and BtoA.              *)
(***************************************************************************)
EXTENDS Integers, Sequences

CONSTANTS Data

Remove(i, seq) ==
  [j \in 1..(Len(seq) - 1) |-> IF j < i THEN seq[j] ELSE seq[j + 1]]

(***************************************************************************
--algorithm ABAlg {
  variables AVar \in Data \X {1}, BVar = AVar,
            AtoB = << >>, BtoA = << >>;

  macro Send(m, chan) { chan := Append(chan, m) }

  macro Rcv(v, chan) { await chan # << >>;
                       v := Head(chan);
                       chan := Tail(chan) }

  process (A = "A")
    variable ack = 0;
  { a: while (TRUE) {
         either Send(AVar, AtoB)
         or     { Rcv(ack, BtoA);
                  if (ack = AVar[2])
                    { with (d \in Data) { AVar := <<d, 1 - AVar[2]>> } }
                }
       }
  }

  process (B = "B")
    variable msg = <<CHOOSE d \in Data : TRUE, 0>>;
  { b: while (TRUE) {
         either Send(BVar[2], BtoA)
         or     { Rcv(msg, AtoB);
                  if (msg[2] # BVar[2]) { BVar := msg }
                }
       }
  }

  process (LoseMsgs = "L")
  { c: while (TRUE) {
         either with (i \in 1..Len(AtoB)) { AtoB := Remove(i, AtoB) }
         or     with (i \in 1..Len(BtoA)) { BtoA := Remove(i, BtoA) }
       }
  }
}
 ***************************************************************************)
\* BEGIN TRANSLATION
VARIABLES AVar, BVar, AtoB, BtoA, pc, ack, msg

vars == << AVar, BVar, AtoB, BtoA, pc, ack, msg >>

ProcSet == {"A"} \cup {"B"} \cup {"L"}

Init == (* Global variables *)
        /\ AVar \in Data \X {1}
        /\ BVar = AVar
        /\ AtoB = << >>
        /\ BtoA = << >>
        (* Process A *)
        /\ ack = 0
        (* Process B *)
        /\ msg = <<CHOOSE d \in Data : TRUE, 0>>
        /\ pc = [self \in ProcSet |-> CASE self = "A" -> "a"
                                       [] self = "B" -> "b"
                                       [] self = "L" -> "c"]

a == /\ pc["A"] = "a"
     /\ \/ /\ AtoB' = Append(AtoB, AVar)
           /\ UNCHANGED << AVar, BtoA, ack >>
        \/ /\ BtoA # << >>
           /\ ack' = Head(BtoA)
           /\ BtoA' = Tail(BtoA)
           /\ IF ack' = AVar[2]
                 THEN /\ \E d \in Data : AVar' = <<d, 1 - AVar[2]>>
                 ELSE /\ TRUE
                      /\ AVar' = AVar
           /\ AtoB' = AtoB
     /\ pc' = [pc EXCEPT !["A"] = "a"]
     /\ UNCHANGED << BVar, msg >>

A == a

b == /\ pc["B"] = "b"
     /\ \/ /\ BtoA' = Append(BtoA, BVar[2])
           /\ UNCHANGED << BVar, AtoB, msg >>
        \/ /\ AtoB # << >>
           /\ msg' = Head(AtoB)
           /\ AtoB' = Tail(AtoB)
           /\ IF msg'[2] # BVar[2]
                 THEN /\ BVar' = msg'
                 ELSE /\ TRUE
                      /\ BVar' = BVar
           /\ BtoA' = BtoA
     /\ pc' = [pc EXCEPT !["B"] = "b"]
     /\ UNCHANGED << AVar, ack >>

B == b

c == /\ pc["L"] = "c"
     /\ \/ /\ \E i \in 1..Len(AtoB) : AtoB' = Remove(i, AtoB)
           /\ BtoA' = BtoA
        \/ /\ \E i \in 1..Len(BtoA) : BtoA' = Remove(i, BtoA)
           /\ AtoB' = AtoB
     /\ pc' = [pc EXCEPT !["L"] = "c"]
     /\ UNCHANGED << AVar, BVar, ack, msg >>

LoseMsgs == c

Next == A \/ B \/ LoseMsgs

Spec == Init /\ [][Next]_vars
\* END TRANSLATION

-----------------------------------------------------------------------------
(***************************************************************************)
(* Safety properties.                                                      *)
(***************************************************************************)
Messages == Data \X {0, 1}

TypeOK == /\ AVar \in Messages
          /\ BVar \in Messages
          /\ AtoB \in Seq(Messages)
          /\ BtoA \in Seq({0, 1})
          /\ ack \in {0, 1}
          /\ msg \in Messages
          /\ pc \in [ProcSet -> {"a", "b", "c"}]

(* When the bits agree, B holds exactly the value A is currently sending. *)
Inv == (AVar[2] = BVar[2]) => (AVar = BVar)
=============================================================================