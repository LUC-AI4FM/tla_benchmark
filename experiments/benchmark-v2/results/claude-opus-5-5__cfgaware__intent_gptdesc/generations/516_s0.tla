---------------------------- MODULE AlternatingBit ----------------------------
(***************************************************************************)
(* Alternating Bit protocol.                                               *)
(*   Sender A holds AVar = <<data, bit>>, the value it currently offers.   *)
(*   Receiver B holds BVar = <<data, bit>>, the last value delivered.      *)
(*   AtoB carries data messages and BtoA carries acknowledgment bits.      *)
(*   The channels may lose or duplicate messages but never corrupt them.   *)
(*   They are modeled FIFO because the protocol needs this to be correct:  *)
(*   with arbitrary reordering, a stale message carrying a reused bit      *)
(*   could be mistaken for a fresh one.                                    *)
(***************************************************************************)
EXTENDS Naturals, Sequences

CONSTANT Data

VARIABLES AVar, BVar, AtoB, BtoA

vars == <<AVar, BVar, AtoB, BtoA>>

Msgs == (Data \X {0, 1}) \cup {0, 1}

MaxLen == 3   \* bound on channel occupancy, keeping the state space finite

Remove(i, s) == [j \in 1..(Len(s) - 1) |-> IF j < i THEN s[j] ELSE s[j + 1]]

DupAt(i, s) == SubSeq(s, 1, i) \o SubSeq(s, i, Len(s))

TypeOK ==
  /\ AVar \in Data \X {0, 1}
  /\ BVar \in Data \X {0, 1}
  /\ AtoB \in Seq(Data \X {0, 1})
  /\ BtoA \in Seq({0, 1})
  /\ \A i \in 1..Len(AtoB) : AtoB[i] \in Msgs
  /\ \A i \in 1..Len(BtoA) : BtoA[i] \in Msgs

Init ==
  /\ AVar \in Data \X {1}
  /\ BVar = AVar
  /\ AtoB = << >>
  /\ BtoA = << >>

(* Sender (re)transmits its current data value. *)
ASnd ==
  /\ Len(AtoB) < MaxLen
  /\ AtoB' = Append(AtoB, AVar)
  /\ UNCHANGED <<AVar, BVar, BtoA>>

(* Sender receives an ack. A matching bit lets it offer a new data value. *)
ARcv ==
  /\ BtoA # << >>
  /\ BtoA' = Tail(BtoA)
  /\ IF Head(BtoA) = AVar[2]
       THEN \E d \in Data : AVar' = <<d, 1 - AVar[2]>>
       ELSE AVar' = AVar
  /\ UNCHANGED <<BVar, AtoB>>

(* Receiver acknowledges with the bit of its last delivered value. *)
BSnd ==
  /\ Len(BtoA) < MaxLen
  /\ BtoA' = Append(BtoA, BVar[2])
  /\ UNCHANGED <<AVar, BVar, AtoB>>

(* Receiver accepts a data message and delivers it only if the bit is new. *)
BRcv ==
  /\ AtoB # << >>
  /\ AtoB' = Tail(AtoB)
  /\ IF Head(AtoB)[2] # BVar[2]
       THEN BVar' = Head(AtoB)
       ELSE BVar' = BVar
  /\ UNCHANGED <<AVar, BtoA>>

(* Unreliable channel: loss. *)
LoseMsg ==
  /\ \/ /\ AtoB # << >>
        /\ \E i \in 1..Len(AtoB) : AtoB' = Remove(i, AtoB)
        /\ UNCHANGED BtoA
     \/ /\ BtoA # << >>
        /\ \E i \in 1..Len(BtoA) : BtoA' = Remove(i, BtoA)
        /\ UNCHANGED AtoB
  /\ UNCHANGED <<AVar, BVar>>

(* Unreliable channel: duplication. *)
DupMsg ==
  /\ \/ /\ AtoB # << >>
        /\ Len(AtoB) < MaxLen
        /\ \E i \in 1..Len(AtoB) : AtoB' = DupAt(i, AtoB)
        /\ UNCHANGED BtoA
     \/ /\ BtoA # << >>
        /\ Len(BtoA) < MaxLen
        /\ \E i \in 1..Len(BtoA) : BtoA' = DupAt(i, BtoA)
        /\ UNCHANGED AtoB
  /\ UNCHANGED <<AVar, BVar>>

Next == ASnd \/ ARcv \/ BSnd \/ BRcv \/ LoseMsg \/ DupMsg

(* Weak fairness keeps both processes retransmitting. Strong fairness on  *)
(* receipt means a message that keeps getting through is eventually       *)
(* received, so the channel cannot permanently lose every copy.           *)
Fairness ==
  /\ WF_vars(ASnd)
  /\ WF_vars(BSnd)
  /\ SF_vars(ARcv)
  /\ SF_vars(BRcv)

Spec == Init /\ [][Next]_vars /\ Fairness

FairSpec == Spec

-----------------------------------------------------------------------------
(* Safety *)

(* A data message carrying the sender's current bit always holds the     *)
(* sender's current value.                                                *)
ChannelInv ==
  \A i \in 1..Len(AtoB) : AtoB[i][2] = AVar[2] => AtoB[i] = AVar

(* If the bits agree, the receiver has delivered the sender's value. *)
Inv == (AVar[2] = BVar[2]) => (AVar = BVar)

(* Integrity: every delivered value is the value the sender is offering. *)
(* Each new delivery carries a fresh bit, so no spurious duplicates.     *)
NoSpuriousDelivery ==
  [][BVar' # BVar => (BVar' = AVar /\ BVar'[2] # BVar[2])]_vars

(* No second delivery happens unless the sender has issued a new value. *)
NoDupWithoutNewSend ==
  [][(BVar' # BVar) => (BVar = AVar \/ BVar[2] # AVar[2]) /\ BVar' = AVar]_vars

(* Liveness: every value the sender offers is eventually delivered. *)
Liveness == \A v \in Data \X {0, 1} : (AVar = v) ~> (BVar = v)

(* Progress: the sender is never permanently stuck on one value. *)
Progress == \A b \in {0, 1} : (AVar[2] = b) ~> (AVar[2] # b)

=============================================================================