--------------------------- MODULE AlternatingBit ---------------------------
(***************************************************************************)
(* Alternating bit protocol over lossy channels with bounded queue         *)
(* capacity.  The sender transmits items from an unbounded stream of       *)
(* application data, each tagged with a one-bit sequence number.  The      *)
(* receiver accepts data only when its bit differs from the bit of the     *)
(* last packet it accepted, so duplicates are detected and discarded.  It  *)
(* returns acknowledgements carrying the bit of the last packet it         *)
(* accepted.  The sender retransmits until it receives an acknowledgement  *)
(* whose bit matches its current bit.  The environment may drop any        *)
(* message in either channel at any position, but never alters contents.   *)
(*                                                                         *)
(* Channels are FIFO with arbitrary loss.  Unrestricted reordering is not  *)
(* modelled: with only one sequence bit, the protocol is incorrect when a  *)
(* stale packet can overtake newer ones.                                   *)
(***************************************************************************)
EXTENDS Naturals, Sequences

CONSTANTS Data,      \* the domain of application data items
          msgQLen,   \* capacity bound for the data channel
          ackQLen    \* capacity bound for the acknowledgement channel

ASSUME /\ Data # {}
       /\ msgQLen \in Nat \ {0}
       /\ ackQLen \in Nat \ {0}

VARIABLES msgQ,  \* data channel: sequence of <<bit, data>>
          ackQ,  \* ack channel: sequence of bits
          sBit,  \* sender's current sequence bit
          sAck,  \* bit of the last ack received by the sender
          rBit,  \* bit of the last packet accepted by the receiver
          sent,  \* the data item the sender is currently sending
          rcvd   \* the last data item delivered by the receiver

abvars == <<msgQ, ackQ, sBit, sAck, rBit, sent, rcvd>>

(***************************************************************************)
(* Type invariant                                                          *)
(***************************************************************************)
ABTypeInv ==
  /\ msgQ \in Seq({0, 1} \X Data)
  /\ ackQ \in Seq({0, 1})
  /\ sBit \in {0, 1}
  /\ sAck \in {0, 1}
  /\ rBit \in {0, 1}
  /\ sent \in Data
  /\ rcvd \in Data

(***************************************************************************)
(* Initial state                                                           *)
(***************************************************************************)
ABInit ==
  /\ msgQ = << >>
  /\ ackQ = << >>
  /\ sBit \in {0, 1}
  /\ sAck = sBit
  /\ rBit = sBit
  /\ sent \in Data
  /\ rcvd \in Data

(***************************************************************************)
(* Sender actions                                                          *)
(***************************************************************************)
\* The previous item has been acknowledged: take a new item from the
\* stream, flip the bit, and transmit.
SndNewValue(d) ==
  /\ sAck = sBit
  /\ sent' = d
  /\ sBit' = 1 - sBit
  /\ msgQ' = Append(msgQ, <<sBit', d>>)
  /\ UNCHANGED <<ackQ, sAck, rBit, rcvd>>

\* The current item is not yet acknowledged: retransmit it.
ReSndMsg ==
  /\ sAck # sBit
  /\ msgQ' = Append(msgQ, <<sBit, sent>>)
  /\ UNCHANGED <<ackQ, sBit, sAck, rBit, sent, rcvd>>

\* Receive an acknowledgement.  The sender records its bit; only an ack
\* whose bit equals sBit enables sending a new value.
RcvAck ==
  /\ ackQ # << >>
  /\ ackQ' = Tail(ackQ)
  /\ sAck' = Head(ackQ)
  /\ UNCHANGED <<msgQ, sBit, rBit, sent, rcvd>>

(***************************************************************************)
(* Receiver actions                                                        *)
(***************************************************************************)
\* Receive a data packet.  If its bit differs from rBit, the packet is new:
\* accept and deliver it.  Otherwise it is a duplicate and is discarded.
RcvMsg ==
  /\ msgQ # << >>
  /\ msgQ' = Tail(msgQ)
  /\ IF Head(msgQ)[1] # rBit
       THEN /\ rBit' = Head(msgQ)[1]
            /\ rcvd' = Head(msgQ)[2]
       ELSE UNCHANGED <<rBit, rcvd>>
  /\ UNCHANGED <<ackQ, sBit, sAck, sent>>

\* (Re)send an acknowledgement carrying the bit of the last accepted packet.
SndAck ==
  /\ ackQ' = Append(ackQ, rBit)
  /\ UNCHANGED <<msgQ, sBit, sAck, rBit, sent, rcvd>>

(***************************************************************************)
(* Environment: loss of a message anywhere in a channel                    *)
(***************************************************************************)
RemoveAt(q, i) == [j \in 1..(Len(q) - 1) |-> IF j < i THEN q[j] ELSE q[j + 1]]

LoseMsg ==
  /\ msgQ # << >>
  /\ \E i \in 1..Len(msgQ) : msgQ' = RemoveAt(msgQ, i)
  /\ UNCHANGED <<ackQ, sBit, sAck, rBit, sent, rcvd>>

LoseAck ==
  /\ ackQ # << >>
  /\ \E i \in 1..Len(ackQ) : ackQ' = RemoveAt(ackQ, i)
  /\ UNCHANGED <<msgQ, sBit, sAck, rBit, sent, rcvd>>

(***************************************************************************)
(* Next-state relation and specification                                   *)
(***************************************************************************)
ABNext ==
  \/ \E d \in Data : SndNewValue(d)
  \/ ReSndMsg
  \/ RcvMsg
  \/ SndAck
  \/ RcvAck
  \/ LoseMsg
  \/ LoseAck

\* Retransmission and acknowledging are weakly fair.  Receipt is strongly
\* fair: the network may drop copies, but not every copy forever.
ABFairness ==
  /\ WF_abvars(ReSndMsg)
  /\ WF_abvars(SndAck)
  /\ SF_abvars(RcvMsg)
  /\ SF_abvars(RcvAck)

ABSpec == ABInit /\ [][ABNext]_abvars /\ ABFairness

(***************************************************************************)
(* State constraint bounding channel capacity for model checking           *)
(***************************************************************************)
SeqConstraint == /\ Len(msgQ) <= msgQLen
                 /\ Len(ackQ) <= ackQLen

(***************************************************************************)
(* Safety invariants                                                       *)
(***************************************************************************)
\* Every packet in the data channel is either the current item tagged with
\* the current bit or an outdated duplicate of the previously accepted item.
\* Every ack in the ack channel carries either the receiver's current bit or
\* an older bit.  This rules out spurious and out-of-order deliveries.
\*
\* Sequence correctness:
\*  - An unacknowledged item is in flight only with the current bit sBit.
\*  - The receiver delivers new data only when the bit changes, and that
\*    data is then exactly 'sent'.
NoSpuriousMsgs ==
  \A i \in 1..Len(msgQ) :
     \/ msgQ[i] = <<sBit, sent>>
     \/ msgQ[i][1] = rBit

\* If the receiver has accepted the current bit, it has delivered the
\* current item.
DeliveredIsSent == (rBit = sBit) => (rcvd = sent)

\* The sender considers an item acknowledged only after the receiver has
\* accepted it.
AckImpliesRcvd == (sAck = sBit) => (rBit = sBit)

\* The channels are ordered: once a packet bearing the current bit appears,
\* every later packet also bears the current bit.  Acks are ordered likewise.
MsgQOrdered ==
  \A i, j \in 1..Len(msgQ) :
     (i < j /\ msgQ[i][1] = sBit) => msgQ[j][1] = sBit

AckQOrdered ==
  \A i, j \in 1..Len(ackQ) :
     (i < j /\ ackQ[i] = rBit) => ackQ[j] = rBit

ABInv ==
  /\ ABTypeInv
  /\ NoSpuriousMsgs
  /\ DeliveredIsSent
  /\ AckImpliesRcvd
  /\ MsgQOrdered
  /\ AckQOrdered

(***************************************************************************)
(* Abstract correctness specification (ABCorrectness)                      *)
(* The sender and receiver communicate directly and reliably.  ABSpec      *)
(* implements ABCSpec, which shows that deliveries happen in order,        *)
(* exactly once per item, and only for items actually sent.                *)
(***************************************************************************)
cvars == <<sBit, sAck, rBit, sent, rcvd>>

CInit ==
  /\ sBit \in {0, 1}
  /\ sAck = sBit
  /\ rBit = sBit
  /\ sent \in Data
  /\ rcvd \in Data

CSndNewValue(d) ==
  /\ sAck = sBit
  /\ sent' = d
  /\ sBit' = 1 - sBit
  /\ UNCHANGED <<sAck, rBit, rcvd>>

CRcvMsg ==
  /\ rBit # sBit
  /\ rBit' = sBit
  /\ rcvd' = sent
  /\ UNCHANGED <<sBit, sAck, sent>>

CRcvAck ==
  /\ rBit # sAck
  /\ sAck' = rBit
  /\ UNCHANGED <<sBit, rBit, sent, rcvd>>

CNext ==
  \/ \E d \in Data : CSndNewValue(d)
  \/ CRcvMsg
  \/ CRcvAck

ABCSpec == CInit /\ [][CNext]_cvars /\ WF_cvars(CRcvMsg) /\ WF_cvars(CRcvAck)

(***************************************************************************)
(* Liveness properties                                                     *)
(***************************************************************************)
\* Eventual delivery: every item sent and not yet acknowledged is
\* eventually delivered to the receiver.
SentLeadsToRcvd ==
  \A d \in Data : (sent = d /\ sBit # sAck) ~> (rcvd = d)

\* Progress: an outstanding item is eventually acknowledged, which lets the
\* sender move on to the next item.
AckProgress == (sBit # sAck) ~> (sBit = sAck)

THEOREM ABSpec => []ABInv
THEOREM ABSpec => ABCSpec
THEOREM ABSpec => SentLeadsToRcvd /\ AckProgress
=============================================================================