------------------------------ MODULE AlternatingBit ------------------------------

EXTENDS Naturals, Sequences

CONSTANT Data

(*
  Alternating-bit protocol between a single sender and receiver over unreliable channels.
  Channels may lose, duplicate, and reorder messages but never corrupt contents.
*)

(*
  Basic sets and helpers
*)
Bits == {0, 1}

MsgType == [bit: Bits, val: Data]

None == "None"  \* distinguished value (may or may not be in Data; it is ignored functionally)

Toggle(b) == IF b = 0 THEN 1 ELSE 0

(*
  Sequence helper: remove the element at position i (1-based) from sequence s.
*)
RemoveAt(s, i) == SubSeq(s, 1, i - 1) \o SubSeq(s, i + 1, Len(s))

(*
  State variables
*)
VARIABLES
  snd_bit,     \* sender's next message bit to use
  snd_wait,    \* TRUE iff sender has an outstanding (unacknowledged) message
  snd_val,     \* value of the outstanding message when snd_wait = TRUE; irrelevant otherwise
  rcv_last,    \* receiver's last delivered bit
  delivered,   \* sequence of delivered data items at the receiver
  msgChan,     \* sequence (multiset with order) of in-flight data messages (records of MsgType)
  ackChan      \* sequence of in-flight acknowledgments (bits)

vars == << snd_bit, snd_wait, snd_val, rcv_last, delivered, msgChan, ackChan >>

(*
  Initial conditions:
  - Sender is idle, ready to send bit 0 next.
  - Receiver has not yet delivered bit 0 (so rcv_last = 1), enabling first acceptance of bit 0.
  - Channels empty; no deliveries yet.
*)
Init ==
  /\ snd_bit = 0
  /\ snd_wait = FALSE
  /\ snd_val = None
  /\ rcv_last = 1
  /\ delivered = << >>
  /\ msgChan = << >>
  /\ ackChan = << >>

(*
  Sender starts sending a new data item only when it is not waiting for an acknowledgment.
  It chooses an arbitrary data item from Data, records it, and emits the first copy.
*)
SendData ==
  /\ ~snd_wait
  /\ \E d \in Data:
       /\ snd_wait' = TRUE
       /\ snd_val' = d
       /\ msgChan' = Append(msgChan, [bit |-> snd_bit, val |-> d])
       /\ UNCHANGED << snd_bit, rcv_last, delivered, ackChan >>

(*
  While waiting for an acknowledgment, the sender may retransmit the outstanding message.
*)
Resend ==
  /\ snd_wait
  /\ msgChan' = Append(msgChan, [bit |-> snd_bit, val |-> snd_val])
  /\ UNCHANGED << snd_bit, snd_wait, snd_val, rcv_last, delivered, ackChan >>

(*
  Receiver delivers a message with bit = b taken from anywhere in the channel.
  If b # rcv_last, it is a fresh message: deliver and update rcv_last.
  If b = rcv_last, it is a duplicate: do not deliver again.
  In both cases, send an acknowledgment carrying bit b.
*)
DeliverMsgBit(b) ==
  /\ \E i \in 1..Len(msgChan): msgChan[i].bit = b
  /\ LET i == CHOOSE k \in 1..Len(msgChan): msgChan[k].bit = b IN
     LET p == msgChan[i] IN
       /\ msgChan' = RemoveAt(msgChan, i)
       /\ IF p.bit # rcv_last THEN
            /\ rcv_last' = p.bit
            /\ delivered' = Append(delivered, p.val)
          ELSE
            /\ rcv_last' = rcv_last
            /\ delivered' = delivered
       /\ ackChan' = Append(ackChan, p.bit)
       /\ UNCHANGED << snd_bit, snd_wait, snd_val >>

(*
  Acknowledgment delivery for bit b; upon matching the sender's outstanding bit,
  the sender stops waiting, toggles snd_bit, and clears snd_val (to None).
*)
DeliverAckBit(b) ==
  /\ \E i \in 1..Len(ackChan): ackChan[i] = b
  /\ LET i == CHOOSE k \in 1..Len(ackChan): ackChan[k] = b IN
     LET a == ackChan[i] IN
       /\ ackChan' = RemoveAt(ackChan, i)
       /\ IF snd_wait /\ a = snd_bit THEN
            /\ snd_wait' = FALSE
            /\ snd_bit' = Toggle(snd_bit)
            /\ snd_val' = None
          ELSE
            /\ UNCHANGED << snd_bit, snd_wait, snd_val >>
       /\ UNCHANGED << rcv_last, delivered, msgChan >>

(*
  Receiver may resend an acknowledgment (for its current rcv_last) at any time.
*)
ResendAck ==
  /\ ackChan' = Append(ackChan, rcv_last)
  /\ UNCHANGED << snd_bit, snd_wait, snd_val, rcv_last, delivered, msgChan >>

(*
  Unreliable channels: messages/acks may be dropped (lost) from anywhere in their channels.
*)
DropMsg ==
  /\ Len(msgChan) > 0
  /\ \E i \in 1..Len(msgChan): msgChan' = RemoveAt(msgChan, i)
  /\ UNCHANGED << snd_bit, snd_wait, snd_val, rcv_last, delivered, ackChan >>

DropAck ==
  /\ Len(ackChan) > 0
  /\ \E i \in 1..Len(ackChan): ackChan' = RemoveAt(ackChan, i)
  /\ UNCHANGED << snd_bit, snd_wait, snd_val, rcv_last, delivered, msgChan >>

(*
  The overall next-state relation
*)
Next ==
  \/ SendData
  \/ Resend
  \/ \E b \in Bits: DeliverMsgBit(b)
  \/ \E b \in Bits: DeliverAckBit(b)
  \/ ResendAck
  \/ DropMsg
  \/ DropAck

(*
  Type invariant: typing of all state components and basic consistency conditions.
*)
TypeInv ==
  /\ snd_bit \in Bits
  /\ snd_wait \in BOOLEAN
  /\ snd_val \in (Data \cup {None})
  /\ snd_wait => snd_val \in Data
  /\ rcv_last \in Bits
  /\ delivered \in Seq(Data)
  /\ msgChan \in Seq(MsgType)
  /\ ackChan \in Seq(Bits)

(*
  Fair-loss and progress assumptions:
  - If messages (resp. acks) of bit b are repeatedly present, then deliveries of bit b occur infinitely often.
  - If the sender (resp. receiver) can continually resend, it will do so eventually (and, if the condition persists, repeatedly).
*)
Fairness ==
  /\ \A b \in Bits: SF_vars(DeliverMsgBit(b))
  /\ \A b \in Bits: SF_vars(DeliverAckBit(b))
  /\ WF_vars(Resend)
  /\ WF_vars(ResendAck)

(*
  The specification to be checked: safety (via Next and invariants) and liveness (via Fairness).
*)
ABCSpec ==
  Init /\ [][Next]_vars /\ Fairness

=============================================================================