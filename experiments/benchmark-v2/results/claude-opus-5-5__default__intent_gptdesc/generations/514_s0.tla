------------------------------- MODULE AlternatingBit -------------------------------
(***************************************************************************)
(* Alternating Bit protocol over unreliable channels.                     *)
(*                                                                         *)
(* A sender transmits items from the abstract set Data to a receiver.     *)
(* Each message carries one data payload and a one-bit sequence value.    *)
(* The receiver returns one-bit acknowledgements. Both channels may lose  *)
(* messages, duplicate them, and delay them for any length of time.       *)
(* They never corrupt payloads or bits.                                   *)
(*                                                                         *)
(* Reordering: the Alternating Bit protocol is only correct if the        *)
(* channel cannot reorder messages that carry different bits. Arbitrary   *)
(* reordering would let a stale message from two rounds earlier be        *)
(* accepted as new. So each channel is a sequence. Duplicates are         *)
(* inserted next to the original, and any element may be dropped. The     *)
(* only reordering this allows is among copies of the same message.       *)
(* Those copies are identical, so swapping them changes nothing.          *)
(*                                                                         *)
(* The variables input, output and outBits are history variables. They   *)
(* exist only so that the correctness properties can be stated.           *)
(*                                                                         *)
(* MaxItems and MaxQ bound the state space so that TLC can check the     *)
(* model. They do not restrict the protocol itself.                       *)
(***************************************************************************)
EXTENDS Naturals, Sequences

CONSTANTS Data,      \* abstract set of data items
          MaxItems,  \* bound on number of items the sender produces
          MaxQ       \* bound on channel occupancy (for model checking)

ASSUME /\ Data # {}
       /\ MaxItems \in Nat
       /\ MaxQ \in Nat \ {0}

Bits    == {0, 1}
Message == Data \X Bits

VARIABLES
  sBit,     \* bit attached to the sender's current item
  sData,    \* sender's current data item
  sAck,     \* TRUE iff the current item has been acknowledged (sender may advance)
  rBit,     \* bit of the last message the receiver accepted
  msgQ,     \* channel sender -> receiver (sequence of messages)
  ackQ,     \* channel receiver -> sender (sequence of bits)
  input,    \* history: sequence of items produced by the sender
  output,   \* history: sequence of items delivered by the receiver
  outBits   \* history: bits of the messages accepted by the receiver

vars == <<sBit, sData, sAck, rBit, msgQ, ackQ, input, output, outBits>>

-----------------------------------------------------------------------------
(* Channel helper operators *)
Remove(q, i) == SubSeq(q, 1, i - 1) \o SubSeq(q, i + 1, Len(q))
Dup(q, i)    == SubSeq(q, 1, i) \o SubSeq(q, i, Len(q))

-----------------------------------------------------------------------------
TypeOK ==
  /\ sBit \in Bits
  /\ sData \in Data
  /\ sAck \in BOOLEAN
  /\ rBit \in Bits
  /\ msgQ \in Seq(Message)
  /\ ackQ \in Seq(Bits)
  /\ input \in Seq(Data)
  /\ output \in Seq(Data)
  /\ outBits \in Seq(Bits)

Init ==
  /\ sBit = 0
  /\ sData \in Data
  /\ sAck = TRUE          \* nothing outstanding yet
  /\ rBit = 0             \* so the first item, sent with bit 1, counts as new
  /\ msgQ = << >>
  /\ ackQ = << >>
  /\ input = << >>
  /\ output = << >>
  /\ outBits = << >>

-----------------------------------------------------------------------------
(* Sender actions *)

\* The sender takes a new item. It may only do so once the previous item
\* has been acknowledged. The bit alternates.
SndNewValue(d) ==
  /\ sAck
  /\ Len(input) < MaxItems
  /\ sData' = d
  /\ sBit' = 1 - sBit
  /\ sAck' = FALSE
  /\ input' = Append(input, d)
  /\ UNCHANGED <<rBit, msgQ, ackQ, output, outBits>>

\* The sender (re)transmits its current unacknowledged message.
SndMsg ==
  /\ ~sAck
  /\ Len(msgQ) < MaxQ
  /\ msgQ' = Append(msgQ, <<sData, sBit>>)
  /\ UNCHANGED <<sBit, sData, sAck, rBit, ackQ, input, output, outBits>>

\* The sender receives an acknowledgement. If the bit matches, the
\* current item is known to be accepted. Otherwise the ack is stale.
RcvAck ==
  /\ ackQ # << >>
  /\ ackQ' = Tail(ackQ)
  /\ sAck' = (sAck \/ Head(ackQ) = sBit)
  /\ UNCHANGED <<sBit, sData, rBit, msgQ, input, output, outBits>>

-----------------------------------------------------------------------------
(* Receiver actions *)

\* The receiver takes the next message from the channel. It delivers the
\* item iff the bit differs from the last accepted bit. Otherwise it
\* discards the message as a duplicate.
RcvMsg ==
  /\ msgQ # << >>
  /\ msgQ' = Tail(msgQ)
  /\ LET m == Head(msgQ) IN
       IF m[2] # rBit
         THEN /\ rBit' = m[2]
              /\ output' = Append(output, m[1])
              /\ outBits' = Append(outBits, m[2])
         ELSE UNCHANGED <<rBit, output, outBits>>
  /\ UNCHANGED <<sBit, sData, sAck, ackQ, input>>

\* The receiver (re)sends an acknowledgement carrying its last accepted bit.
SndAck ==
  /\ Len(ackQ) < MaxQ
  /\ ackQ' = Append(ackQ, rBit)
  /\ UNCHANGED <<sBit, sData, sAck, rBit, msgQ, input, output, outBits>>

-----------------------------------------------------------------------------
(* Unreliable channel actions: loss and duplication. Neither changes a    *)
(* payload or a bit.                                                      *)

LoseMsg ==
  /\ \E i \in 1..Len(msgQ) : msgQ' = Remove(msgQ, i)
  /\ UNCHANGED <<sBit, sData, sAck, rBit, ackQ, input, output, outBits>>

LoseAck ==
  /\ \E i \in 1..Len(ackQ) : ackQ' = Remove(ackQ, i)
  /\ UNCHANGED <<sBit, sData, sAck, rBit, msgQ, input, output, outBits>>

DupMsg ==
  /\ Len(msgQ) < MaxQ
  /\ \E i \in 1..Len(msgQ) : msgQ' = Dup(msgQ, i)
  /\ UNCHANGED <<sBit, sData, sAck, rBit, ackQ, input, output, outBits>>

DupAck ==
  /\ Len(ackQ) < MaxQ
  /\ \E i \in 1..Len(ackQ) : ackQ' = Dup(ackQ, i)
  /\ UNCHANGED <<sBit, sData, sAck, rBit, msgQ, input, output, outBits>>

-----------------------------------------------------------------------------
Next ==
  \/ \E d \in Data : SndNewValue(d)
  \/ SndMsg
  \/ RcvAck
  \/ RcvMsg
  \/ SndAck
  \/ LoseMsg
  \/ LoseAck
  \/ DupMsg
  \/ DupAck

(***************************************************************************)
(* Fairness:                                                               *)
(*  - The sender keeps retransmitting the current message (WF SndMsg).     *)
(*  - The receiver keeps re-acknowledging (WF SndAck).                     *)
(*  - The channels deliver some transmission infinitely often if one is   *)
(*    infinitely often in transit (SF RcvMsg, SF RcvAck). Strong fairness *)
(*    is needed because loss can repeatedly empty a channel and so        *)
(*    disable reception.                                                  *)
(*  - Loss and duplication get no fairness.                                *)
(*  - Producing new items is not required to happen.                       *)
(***************************************************************************)
Fairness ==
  /\ WF_vars(SndMsg)
  /\ WF_vars(SndAck)
  /\ SF_vars(RcvMsg)
  /\ SF_vars(RcvAck)

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Correctness properties *)

IsPrefix(s, t) ==
  /\ Len(s) <= Len(t)
  /\ SubSeq(t, 1, Len(s)) = s

\* Safety / no spurious deliveries: every delivered item was sent. Each
\* sent item is delivered at most once, in order. The receiver is never
\* more than one item behind the sender.
NoSpuriousDelivery ==
  /\ IsPrefix(output, input)
  /\ Len(input) - Len(output) \in {0, 1}

\* Receiver delivery ordering: the delivered sequence equals the produced
\* sequence position by position, with no reordering.
DeliveryOrder ==
  \A i \in 1..Len(output) : output[i] = input[i]

\* Bit alternation: successive accepted messages have alternating bits.
\* The first accepted bit is 1.
BitAlternation ==
  /\ Len(outBits) = Len(output)
  /\ \A i \in 1..(Len(outBits) - 1) : outBits[i] # outBits[i + 1]
  /\ \A i \in 1..Len(outBits) : outBits[i] = i % 2

\* Auxiliary protocol invariant. While the sender is waiting, the receiver
\* has either not yet accepted the current item or has just accepted it.
\* Once the sender knows the item was accepted, the receiver has it.
ProtocolInv ==
  /\ sAck => (rBit = sBit /\ Len(output) = Len(input))
  /\ (Len(output) = Len(input)) <=> (rBit = sBit)
  /\ sBit = Len(input) % 2
  /\ rBit = Len(output) % 2

Safety == TypeOK /\ NoSpuriousDelivery /\ DeliveryOrder /\ BitAlternation /\ ProtocolInv

\* Liveness / eventual delivery: every item the sender produces is
\* eventually delivered.
EventualDelivery ==
  \A n \in 1..MaxItems : (Len(input) >= n) ~> (Len(output) >= n)

\* Sender progress: every outstanding item is eventually acknowledged.
EventualAck == (~sAck) ~> sAck

-----------------------------------------------------------------------------
THEOREM TypeCorrect      == Spec => []TypeOK
THEOREM SafetyTheorem    == Spec => []Safety
THEOREM NoSpurious       == Spec => []NoSpuriousDelivery
THEOREM OrderTheorem     == Spec => []DeliveryOrder
THEOREM AlternationThm   == Spec => []BitAlternation
THEOREM LivenessTheorem  == Spec => EventualDelivery
THEOREM AckLiveness      == Spec => EventualAck
=============================================================================