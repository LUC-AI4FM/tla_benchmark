------------------------- MODULE AlternatingBitProtocol -------------------------
(***************************************************************************)
(* Alternating-bit reliable data transfer between one sender and one       *)
(* receiver over unreliable channels.                                      *)
(*                                                                         *)
(* Each channel is a set of messages, so it can lose, duplicate and        *)
(* reorder messages:                                                       *)
(*   - Loss: an explicit Lose action removes a message from the set.       *)
(*   - Duplication: receiving a message does not remove it, so it can be   *)
(*     received again.                                                     *)
(*   - Reordering: a set has no order.                                     *)
(* Message contents are never altered, so there is no corruption.          *)
(*                                                                         *)
(* A one-bit protocol is only correct if stale copies from earlier rounds  *)
(* cannot come back later. This model therefore assumes messages have a    *)
(* bounded lifetime: when the sender starts a new data item, copies left   *)
(* over from earlier rounds have expired. Within a round, the channels may *)
(* still lose, duplicate and reorder messages without limit.               *)
(*                                                                         *)
(* Fair loss is expressed as fairness conditions. If a message (or an      *)
(* acknowledgment) is sent again and again, it is eventually received.     *)
(***************************************************************************)
EXTENDS Naturals, Sequences

CONSTANT Data            \* set of data items the sender may transmit

ASSUME Data # {}

NoData == CHOOSE v : v \notin Data

Bits == {0, 1}
Msgs == [bit : Bits, data : Data]

VARIABLES
    sBit,     \* sender: bit of the current (most recent) message
    sData,    \* sender: data of the current outstanding message
    sReady,   \* sender: TRUE iff it believes the last message was acked
    sent,     \* history: sequence of data items the sender started to send
    rBit,     \* receiver: bit of the last accepted (delivered) message
    rcvd,     \* history: sequence of data items delivered by the receiver
    msgC,     \* data channel  (sender -> receiver), a set of messages
    ackC      \* ack channel   (receiver -> sender), a set of bits

senderVars   == <<sBit, sData, sReady, sent>>
receiverVars == <<rBit, rcvd>>
vars == <<sBit, sData, sReady, sent, rBit, rcvd, msgC, ackC>>

---------------------------------------------------------------------------
(* Type invariant *)

TypeOK ==
    /\ sBit   \in Bits
    /\ sData  \in Data \cup {NoData}
    /\ sReady \in BOOLEAN
    /\ sent   \in Seq(Data)
    /\ rBit   \in Bits
    /\ rcvd   \in Seq(Data)
    /\ msgC   \subseteq Msgs
    /\ ackC   \subseteq Bits

---------------------------------------------------------------------------
(* Initial state *)

Init ==
    /\ sBit   = 0
    /\ sData  = NoData
    /\ sReady = TRUE
    /\ sent   = <<>>
    /\ rBit   = 0
    /\ rcvd   = <<>>
    /\ msgC   = {}
    /\ ackC   = {}

---------------------------------------------------------------------------
(* Sender actions *)

(* Start sending a new item. This is allowed only once the previous item  *)
(* is believed acknowledged. The bit flips, and stale messages from        *)
(* earlier rounds have expired (bounded-lifetime assumption).              *)
SendNew ==
    /\ sReady
    /\ \E d \in Data :
         /\ sData'  = d
         /\ sBit'   = 1 - sBit
         /\ sReady' = FALSE
         /\ sent'   = Append(sent, d)
         /\ msgC'   = {[bit |-> 1 - sBit, data |-> d]}
         /\ ackC'   = {}
    /\ UNCHANGED receiverVars

(* Retransmit the outstanding message, which the sender retains. *)
ReSend ==
    /\ ~sReady
    /\ msgC' = msgC \cup {[bit |-> sBit, data |-> sData]}
    /\ UNCHANGED <<senderVars, receiverVars, ackC>>

(* Receive an ack whose bit matches the outstanding message. *)
RcvAck ==
    /\ ~sReady
    /\ sBit \in ackC
    /\ sReady' = TRUE
    /\ UNCHANGED <<sBit, sData, sent, receiverVars, msgC, ackC>>

---------------------------------------------------------------------------
(* Receiver actions *)

(* A fresh message is one whose bit differs from the last delivered bit.  *)
(* The receiver delivers it and acknowledges it with its bit.              *)
RcvFresh ==
    \E m \in msgC :
       /\ m.bit # rBit
       /\ rBit' = m.bit
       /\ rcvd' = Append(rcvd, m.data)
       /\ ackC' = ackC \cup {m.bit}
       /\ UNCHANGED <<senderVars, msgC>>

(* A duplicate (stale-bit) message is not delivered. The receiver re-acks *)
(* the bit of the last message it accepted.                                *)
RcvDup ==
    \E m \in msgC :
       /\ m.bit = rBit
       /\ ackC' = ackC \cup {rBit}
       /\ UNCHANGED <<senderVars, receiverVars, msgC>>

---------------------------------------------------------------------------
(* Channel faults: arbitrary loss *)

LoseMsg ==
    \E m \in msgC :
       /\ msgC' = msgC \ {m}
       /\ UNCHANGED <<senderVars, receiverVars, ackC>>

LoseAck ==
    \E b \in ackC :
       /\ ackC' = ackC \ {b}
       /\ UNCHANGED <<senderVars, receiverVars, msgC>>

---------------------------------------------------------------------------
(* Next-state relation and specification *)

Next ==
    \/ SendNew
    \/ ReSend
    \/ RcvAck
    \/ RcvFresh
    \/ RcvDup
    \/ LoseMsg
    \/ LoseAck

(* Fairness:                                                               *)
(*  - The sender keeps retransmitting the outstanding message (WF ReSend). *)
(*  - Fair loss: a message or ack that is present again and again is       *)
(*    eventually received (SF on the receive actions).                     *)
Fairness ==
    /\ WF_vars(ReSend)
    /\ SF_vars(RcvFresh)
    /\ SF_vars(RcvDup)
    /\ SF_vars(RcvAck)

Spec == Init /\ [][Next]_vars /\ Fairness

---------------------------------------------------------------------------
(* Safety properties *)

(* Every delivered item equals some item the sender sent. *)
DeliveredWasSent ==
    \A i \in 1..Len(rcvd) : \E j \in 1..Len(sent) : rcvd[i] = sent[j]

(* No duplication and no reordering: the delivered sequence is a prefix   *)
(* of the sent sequence. Each send instance is therefore delivered at     *)
(* most once, and in order.                                                *)
NoDuplication ==
    /\ Len(rcvd) <= Len(sent)
    /\ rcvd = SubSeq(sent, 1, Len(rcvd))

(* At most one item is outstanding. *)
AtMostOneOutstanding ==
    Len(sent) - Len(rcvd) \in {0, 1}

(* Agreement on sequence bits: the sender's and receiver's bits and the   *)
(* acks in transit stay consistent. This rules out a deadlock in which    *)
(* the sender waits for an ack the receiver will never produce.            *)
BitAgreement ==
    /\ sReady => (sBit = rBit /\ Len(rcvd) = Len(sent))
    /\ (sBit \in ackC) => (rBit = sBit)
    /\ (rBit = sBit) => (Len(rcvd) = Len(sent))
    /\ (rBit # sBit) => (~sReady /\ Len(rcvd) + 1 = Len(sent))
    /\ ~sReady => (msgC \subseteq {[bit |-> sBit, data |-> sData]})
    /\ ~sReady => (sent # <<>> /\ sent[Len(sent)] = sData)

Safety ==
    /\ TypeOK
    /\ DeliveredWasSent
    /\ NoDuplication
    /\ AtMostOneOutstanding
    /\ BitAgreement

---------------------------------------------------------------------------
(* Liveness properties *)

(* Every item the sender starts to send is eventually delivered. *)
EventualDelivery ==
    \A n \in Nat : (Len(sent) >= n) ~> (Len(rcvd) >= n)

(* The sender eventually learns that its outstanding item was acked,      *)
(* so the protocol never deadlocks.                                        *)
EventualAck ==
    (~sReady) ~> sReady

Liveness == EventualDelivery /\ EventualAck

---------------------------------------------------------------------------
THEOREM Spec => []Safety
THEOREM Spec => Liveness
=============================================================================