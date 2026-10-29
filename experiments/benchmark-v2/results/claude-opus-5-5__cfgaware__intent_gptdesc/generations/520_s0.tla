------------------------------ MODULE AlternatingBit ------------------------------
(***************************************************************************)
(* Alternating-bit protocol between sender A and receiver B over lossy,    *)
(* non-FIFO channels. Each channel is a finite set of in-flight messages,   *)
(* so messages may be reordered. Re-sending a message already in flight is  *)
(* allowed. Any single in-flight element may be lost.                       *)
(*                                                                         *)
(*   AVar2 : sender state     <<data, bit>> it is currently trying to send *)
(*   BVar2 : receiver state   <<data, bit>> of the last accepted message   *)
(*   AtoB  : in-flight data messages (subset of Msgs)                      *)
(*   BtoA  : in-flight acknowledgments (subset of {0,1})                   *)
(***************************************************************************)
EXTENDS Naturals

CONSTANT Data

VARIABLES AVar2, BVar2, AtoB, BtoA

vars == <<AVar2, BVar2, AtoB, BtoA>>

Bits == {0, 1}

Msgs == Data \X Bits

-----------------------------------------------------------------------------
TypeOK ==
  /\ AVar2 \in Msgs
  /\ BVar2 \in Msgs
  /\ AtoB \subseteq Msgs
  /\ BtoA \subseteq Bits

(* Initially the receiver is considered to have already accepted the      *)
(* sender's current message, so the sender's first step is to pick a new  *)
(* value after its first acknowledgment.                                  *)
Init ==
  /\ AVar2 \in Data \X {1}
  /\ BVar2 = AVar2
  /\ AtoB = {}
  /\ BtoA = {}

-----------------------------------------------------------------------------
(* Sender (re)transmits its current message. *)
ASnd ==
  /\ AtoB' = AtoB \cup {AVar2}
  /\ UNCHANGED <<AVar2, BVar2, BtoA>>

(* Sender receives acknowledgment b. If b acknowledges the current bit,   *)
(* it commits to a new data value and flips its bit; otherwise it ignores *)
(* the stale acknowledgment.                                               *)
ARcvAck(b) ==
  /\ b \in BtoA
  /\ BtoA' = BtoA \ {b}
  /\ IF b = AVar2[2]
       THEN \E d \in Data : AVar2' = <<d, 1 - AVar2[2]>>
       ELSE UNCHANGED AVar2
  /\ UNCHANGED <<BVar2, AtoB>>

ARcv == \E b \in Bits : ARcvAck(b)

(* Receiver sends an acknowledgment carrying the bit of the last accepted message. *)
BSnd ==
  /\ BtoA' = BtoA \cup {BVar2[2]}
  /\ UNCHANGED <<AVar2, BVar2, AtoB>>

(* Receiver receives data message m. It accepts m when the bit differs    *)
(* from its last-seen bit. Otherwise it discards m as a duplicate.         *)
BRcvMsg(m) ==
  /\ m \in AtoB
  /\ AtoB' = AtoB \ {m}
  /\ IF m[2] # BVar2[2]
       THEN BVar2' = m
       ELSE UNCHANGED BVar2
  /\ UNCHANGED <<AVar2, BtoA>>

BRcv == \E m \in Msgs : BRcvMsg(m)

(* Loss of an individual in-flight element. *)
LoseMsg(m) ==
  /\ m \in AtoB
  /\ AtoB' = AtoB \ {m}
  /\ UNCHANGED <<AVar2, BVar2, BtoA>>

LoseAck(b) ==
  /\ b \in BtoA
  /\ BtoA' = BtoA \ {b}
  /\ UNCHANGED <<AVar2, BVar2, AtoB>>

Lose == (\E m \in Msgs : LoseMsg(m)) \/ (\E b \in Bits : LoseAck(b))

Next == ASnd \/ ARcv \/ BSnd \/ BRcv \/ Lose

(* Fairness: weak fairness on sending and strong fairness on receiving   *)
(* each particular element. Strong fairness on receipt captures "losses  *)
(* do not persist forever": a message that is repeatedly in flight is     *)
(* eventually received. There is no fairness on loss.                    *)
Fairness ==
  /\ WF_vars(ASnd)
  /\ WF_vars(BSnd)
  /\ \A m \in Msgs : SF_vars(BRcvMsg(m))
  /\ \A b \in Bits : SF_vars(ARcvAck(b))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Bit alternation invariant: the receiver either has exactly the         *)
(* sender's current message, or is one bit behind it.                     *)
BitAlternation ==
  \/ BVar2 = AVar2
  \/ BVar2[2] # AVar2[2]

(* No spurious data. Any in-flight message carrying the sender's current  *)
(* bit is the sender's current message. Any in-flight acknowledgment of   *)
(* the sender's current bit means the receiver holds the sender's current *)
(* message.                                                                *)
ChannelConsistency ==
  /\ \A m \in AtoB : m[2] = AVar2[2] => m = AVar2
  /\ \A b \in BtoA : b = AVar2[2] => BVar2 = AVar2

(* Safety: whenever the receiver's bit matches the sender's, the delivered *)
(* data is exactly the sender's committed choice.                          *)
NoSpuriousData == BVar2[2] = AVar2[2] => BVar2 = AVar2

Inv == TypeOK /\ BitAlternation /\ ChannelConsistency /\ NoSpuriousData

(* Every acceptance by the receiver is a message the sender is currently  *)
(* committed to.                                                           *)
DeliverOnlySent == [][BVar2' # BVar2 => BVar2' = AVar2]_vars

(* Non-duplication: the receiver changes its delivered message only on a  *)
(* bit change. It therefore never re-accepts a duplicate retransmission.  *)
NoDuplication == [][BVar2' # BVar2 => BVar2'[2] # BVar2[2]]_vars

(* Liveness: every message the sender commits to is eventually accepted  *)
(* by the receiver.                                                       *)
ReceiverProgress == \A v \in Msgs : (AVar2 = v) ~> (BVar2 = v)

(* Liveness: once the receiver holds the sender's message, the sender    *)
(* eventually observes the acknowledgment and moves to a new bit.        *)
SenderProgress == \A i \in Bits : (AVar2[2] = i) ~> (AVar2[2] # i)

THEOREM Spec => []Inv
THEOREM Spec => DeliverOnlySent /\ NoDuplication
THEOREM Spec => ReceiverProgress /\ SenderProgress
=============================================================================