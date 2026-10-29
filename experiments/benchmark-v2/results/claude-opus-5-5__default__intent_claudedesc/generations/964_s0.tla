--------------------------- MODULE AlternatingBit ---------------------------
(***************************************************************************)
(* Alternating Bit Protocol.                                               *)
(*                                                                         *)
(* A sender (A) and a receiver (B) communicate over two unreliable FIFO    *)
(* channels: AtoB carries data messages <<d, bit>> and BtoA carries        *)
(* acknowledgment bits. Either channel may lose any message at any time.   *)
(* Channels never corrupt, reorder or duplicate messages.                  *)
(*                                                                         *)
(* AVar : the message <<data, bit>> the sender is currently trying to send *)
(* BVar : the last message <<data, bit>> the receiver accepted             *)
(***************************************************************************)
EXTENDS Integers, Sequences

CONSTANT Data

VARIABLES AVar, BVar, AtoB, BtoA

vars == <<AVar, BVar, AtoB, BtoA>>

Bits == {0, 1}

Msgs == Data \X Bits

-----------------------------------------------------------------------------
(* Remove the i-th element of a sequence. *)
RemoveIth(s, i) ==
  [j \in 1..(Len(s) - 1) |-> IF j < i THEN s[j] ELSE s[j + 1]]

-----------------------------------------------------------------------------
TypeOK ==
  /\ AVar \in Msgs
  /\ BVar \in Msgs
  /\ AtoB \in Seq(Msgs)
  /\ BtoA \in Seq(Bits)

Init ==
  /\ AVar \in Data \X {1}
  /\ BVar = AVar
  /\ AtoB = << >>
  /\ BtoA = << >>

(* Sender (re)transmits the current message. *)
ASnd ==
  /\ AtoB' = Append(AtoB, AVar)
  /\ UNCHANGED <<AVar, BVar, BtoA>>

(* Sender receives an acknowledgment. If it acknowledges the current       *)
(* message, the sender picks a new data value and flips the bit.           *)
ARcv ==
  /\ BtoA # << >>
  /\ IF Head(BtoA) = AVar[2]
       THEN \E d \in Data : AVar' = <<d, 1 - AVar[2]>>
       ELSE AVar' = AVar
  /\ BtoA' = Tail(BtoA)
  /\ UNCHANGED <<BVar, AtoB>>

(* Receiver sends (or resends) an acknowledgment of the last accepted msg. *)
BSnd ==
  /\ BtoA' = Append(BtoA, BVar[2])
  /\ UNCHANGED <<AVar, BVar, AtoB>>

(* Receiver receives a data message; accepts it iff it carries a new bit. *)
BRcv ==
  /\ AtoB # << >>
  /\ IF Head(AtoB)[2] # BVar[2]
       THEN BVar' = Head(AtoB)
       ELSE BVar' = BVar
  /\ AtoB' = Tail(AtoB)
  /\ UNCHANGED <<AVar, BtoA>>

(* Either channel may lose any message in transit. *)
LoseMsg ==
  /\ \/ /\ \E i \in 1..Len(AtoB) : AtoB' = RemoveIth(AtoB, i)
        /\ BtoA' = BtoA
     \/ /\ \E i \in 1..Len(BtoA) : BtoA' = RemoveIth(BtoA, i)
        /\ AtoB' = AtoB
  /\ UNCHANGED <<AVar, BVar>>

Next == ASnd \/ ARcv \/ BSnd \/ BRcv \/ LoseMsg

Fairness ==
  /\ WF_vars(ASnd)
  /\ WF_vars(BSnd)
  /\ SF_vars(ARcv)
  /\ SF_vars(BRcv)

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(***************************************************************************)
(* Correctness properties                                                  *)
(***************************************************************************)

(* Whenever the sender's and receiver's bits agree, the receiver holds     *)
(* exactly the sender's current data value (no wrong data is delivered).   *)
Consistency ==
  (AVar[2] = BVar[2]) => (AVar = BVar)

(* Every message in the data channel is either the sender's current       *)
(* message or the message the receiver already holds.                     *)
AtoBInv ==
  \A i \in 1..Len(AtoB) : AtoB[i] \in {AVar, BVar}

Inv == TypeOK /\ Consistency /\ AtoBInv

(* High-level (abstract) reliable transmission spec over AVar and BVar:    *)
(* the sender chooses a new value only after the receiver has obtained     *)
(* the previous one, and the receiver obtains exactly what was sent.       *)
ABInit ==
  /\ AVar \in Data \X {1}
  /\ BVar = AVar

A == /\ AVar = BVar
     /\ \E d \in Data : AVar' = <<d, 1 - AVar[2]>>
     /\ BVar' = BVar

B == /\ AVar # BVar
     /\ BVar' = AVar
     /\ AVar' = AVar

ABNext == A \/ B

ABSpec == ABInit /\ [][ABNext]_<<AVar, BVar>> /\ WF_<<AVar, BVar>>(ABNext)

(* Reliable delivery: every message the sender tries to send is           *)
(* eventually received by the receiver.                                   *)
Delivery ==
  \A m \in Msgs : (AVar = m) ~> (BVar = m)

(* Progress: the sender eventually moves on to a new message. *)
Progress ==
  \A b \in Bits : (AVar[2] = b) ~> (AVar[2] # b)

THEOREM Spec => []Inv
THEOREM Spec => ABSpec
THEOREM Spec => Delivery /\ Progress
=============================================================================