------------------------------ MODULE AlternatingBit ------------------------------
(***************************************************************************)
(* Alternating Bit Protocol: a sender and a receiver exchange data         *)
(* messages and acknowledgements over lossy, bounded and possibly          *)
(* reordering channels.                                                    *)
(*                                                                         *)
(* The ghost variables sent and delivered record the application stream    *)
(* the sender consumed and the receiver delivered. They are used only to   *)
(* state correctness.                                                      *)
(*                                                                         *)
(* NOTE: The correctness of the ABP depends on FIFO channels. When         *)
(* Reorder = TRUE, a stale message can carry the same bit as the expected  *)
(* one, so the ordering invariants can be violated. That is a known        *)
(* limitation of the protocol, and the model makes it observable.          *)
(***************************************************************************)
EXTENDS Naturals, Sequences

CONSTANTS
    Data,       \* domain of application data items
    DataCap,    \* capacity of the sender -> receiver data channel
    AckCap,     \* capacity of the receiver -> sender ack channel
    Reorder     \* TRUE iff the network may reorder messages

ASSUME /\ Data # {}
       /\ DataCap \in Nat \ {0}
       /\ AckCap \in Nat \ {0}
       /\ Reorder \in BOOLEAN

VARIABLES
    sBit,       \* sender's current sequence bit
    sVal,       \* item the sender is currently transmitting
    rBit,       \* bit the receiver expects next
    dataChan,   \* data channel: sequence of [bit, val]
    ackChan,    \* ack channel: sequence of bits
    sent,       \* ghost: application items taken by the sender, in order
    delivered   \* ghost: application items delivered by the receiver, in order

vars == <<sBit, sVal, rBit, dataChan, ackChan, sent, delivered>>

Bits == {0, 1}
Flip(b) == 1 - b
Msgs == [bit : Bits, val : Data]

RemoveAt(s, i) == SubSeq(s, 1, i - 1) \o SubSeq(s, i + 1, Len(s))

\* Positions a message may be received from.
\* With FIFO only the head is available; with reordering any position is.
RcvPositions(ch) ==
    IF Reorder THEN 1..Len(ch)
    ELSE IF Len(ch) > 0 THEN {1} ELSE {}

Range(s) == {s[i] : i \in DOMAIN s}

TypeOK ==
    /\ sBit \in Bits
    /\ sVal \in Data
    /\ rBit \in Bits
    /\ dataChan \in Seq(Msgs) /\ Len(dataChan) <= DataCap
    /\ ackChan \in Seq(Bits) /\ Len(ackChan) <= AckCap
    /\ sent \in Seq(Data)
    /\ delivered \in Seq(Data)

-----------------------------------------------------------------------------
Init ==
    /\ sBit = 0
    /\ sVal \in Data
    /\ sent = <<sVal>>
    /\ rBit = 0
    /\ delivered = <<>>
    /\ dataChan = <<>>
    /\ ackChan = <<>>

(* Sender (re)transmits the current item tagged with the current bit. *)
SendData ==
    /\ Len(dataChan) < DataCap
    /\ dataChan' = Append(dataChan, [bit |-> sBit, val |-> sVal])
    /\ UNCHANGED <<sBit, sVal, rBit, ackChan, sent, delivered>>

(* The receiver takes a data message. It accepts and delivers the message  *)
(* only when the bit matches the expected bit. Otherwise it discards the   *)
(* message as a duplicate.                                                 *)
RcvDataAt(i) ==
    LET m == dataChan[i] IN
    /\ dataChan' = RemoveAt(dataChan, i)
    /\ IF m.bit = rBit
         THEN /\ delivered' = Append(delivered, m.val)
              /\ rBit' = Flip(rBit)
         ELSE UNCHANGED <<delivered, rBit>>
    /\ UNCHANGED <<sBit, sVal, ackChan, sent>>

RcvData == \E i \in RcvPositions(dataChan) : RcvDataAt(i)

(* The receiver acknowledges the bit of the last correctly received packet. *)
SendAck ==
    /\ Len(ackChan) < AckCap
    /\ ackChan' = Append(ackChan, Flip(rBit))
    /\ UNCHANGED <<sBit, sVal, rBit, dataChan, sent, delivered>>

(* The sender takes an ack. If the ack matches the current bit, the sender *)
(* advances to a fresh item from the unbounded application stream.        *)
(* Otherwise it ignores the ack.                                          *)
RcvAckAt(i) ==
    LET a == ackChan[i] IN
    /\ ackChan' = RemoveAt(ackChan, i)
    /\ IF a = sBit
         THEN /\ sBit' = Flip(sBit)
              /\ \E d \in Data : /\ sVal' = d
                                 /\ sent' = Append(sent, d)
         ELSE UNCHANGED <<sBit, sVal, sent>>
    /\ UNCHANGED <<rBit, dataChan, delivered>>

RcvAck == \E i \in RcvPositions(ackChan) : RcvAckAt(i)

(* The environment may drop any message. It never alters message contents. *)
LoseData ==
    /\ \E i \in 1..Len(dataChan) : dataChan' = RemoveAt(dataChan, i)
    /\ UNCHANGED <<sBit, sVal, rBit, ackChan, sent, delivered>>

LoseAck ==
    /\ \E i \in 1..Len(ackChan) : ackChan' = RemoveAt(ackChan, i)
    /\ UNCHANGED <<sBit, sVal, rBit, dataChan, sent, delivered>>

Next ==
    \/ SendData \/ RcvData
    \/ SendAck  \/ RcvAck
    \/ LoseData \/ LoseAck

(* Fairness:                                                               *)
(*  - The sender keeps retransmitting (WF on SendData).                    *)
(*  - The receiver keeps acknowledging (WF on SendAck).                    *)
(*  - The network does not permanently drop all copies. If receipt is      *)
(*    enabled infinitely often, it eventually happens (SF on receives).    *)
Fairness ==
    /\ WF_vars(SendData)
    /\ WF_vars(SendAck)
    /\ SF_vars(RcvData)
    /\ SF_vars(RcvAck)

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(*************************** Safety properties *****************************)

\* No spurious deliveries: every delivered item was actually sent.
NoSpuriousDelivery ==
    \A i \in 1..Len(delivered) : delivered[i] \in Range(sent)

\* In-order delivery with duplicates suppressed: delivered is a prefix of sent.
InOrderDelivery ==
    /\ Len(delivered) <= Len(sent)
    /\ \A i \in 1..Len(delivered) : delivered[i] = sent[i]

\* Sequence-bit correctness: the bits track the protocol phase exactly.
SeqBitCorrect ==
    /\ sBit = (Len(sent) - 1) % 2
    /\ rBit = Len(delivered) % 2
    /\ \/ /\ Len(delivered) = Len(sent) - 1   \* current item not yet delivered
          /\ rBit = sBit
       \/ /\ Len(delivered) = Len(sent)       \* current item delivered, awaiting ack
          /\ rBit = Flip(sBit)

\* Channel consistency: a data message carrying the current bit carries the
\* current item. An ack carrying the current bit is only in transit after
\* the current item was delivered. Duplicates therefore cannot be redelivered,
\* and premature acks cannot exist.
ChannelConsistent ==
    /\ \A i \in 1..Len(dataChan) :
          dataChan[i].bit = sBit => dataChan[i].val = sVal
    /\ \A i \in 1..Len(ackChan) :
          ackChan[i] = sBit => Len(delivered) = Len(sent)

\* Action-level guarantee: data is accepted only when its bit matches, and
\* the sender advances only when the ack matches.
AcceptOnlyExpected ==
    [][ /\ (Len(delivered') > Len(delivered)) =>
              /\ Len(delivered') = Len(delivered) + 1
              /\ \E i \in RcvPositions(dataChan) :
                    dataChan[i].bit = rBit /\ dataChan[i].val = Last(delivered')
              /\ rBit' = Flip(rBit)
        /\ (Len(sent') > Len(sent)) =>
              /\ Len(sent') = Len(sent) + 1
              /\ \E i \in RcvPositions(ackChan) : ackChan[i] = sBit
              /\ sBit' = Flip(sBit)
      ]_vars

Last(s) == s[Len(s)]

Safety ==
    /\ TypeOK
    /\ NoSpuriousDelivery
    /\ InOrderDelivery
    /\ SeqBitCorrect
    /\ ChannelConsistent

-----------------------------------------------------------------------------
(*************************** Liveness properties ***************************)

\* Eventual delivery: every item the sender has taken is eventually delivered.
\* The sender takes a new item only after the current one is delivered, so
\* this covers every item in the stream.
EventualDelivery ==
    (Len(delivered) < Len(sent)) ~> (Len(delivered) = Len(sent))

\* General form, quantified over stream positions (not TLC-checkable as is).
EventualDeliveryAll ==
    \A k \in Nat \ {0} : (Len(sent) >= k) ~> (Len(delivered) >= k)

\* Progress: matching acks eventually arrive, so the sender always advances.
SenderProgress ==
    \A b \in Bits : (sBit = b) ~> (sBit = Flip(b))

\* The sender advances infinitely often.
InfiniteProgress ==
    []<>(<<SendData \/ RcvAck>>_vars /\ sent' # sent)

THEOREM Spec => []Safety
THEOREM Spec => AcceptOnlyExpected
THEOREM Spec => EventualDelivery /\ SenderProgress
=============================================================================