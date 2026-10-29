------------------------- MODULE AlternatingBitProtocol -------------------------
EXTENDS Naturals, Sequences

CONSTANTS Data,    \* fixed finite set of messages the sender may produce
          MaxLen   \* maximum length of each FIFO channel

ASSUME MaxLenAssump == MaxLen \in Nat /\ MaxLen > 0
ASSUME DataAssump   == Data # {}

Bits == {0, 1}

VARIABLES sent,  \* current message value held by the sender
          sBit,  \* sender's current alternating bit
          sAck,  \* last acknowledgement bit received by the sender
          rcvd,  \* current message value held by the receiver
          rBit,  \* receiver's current bit
          msgC,  \* channel sender -> receiver : sequence of <<bit, data>>
          ackC   \* channel receiver -> sender : sequence of bits

vars == <<sent, sBit, sAck, rcvd, rBit, msgC, ackC>>

-----------------------------------------------------------------------------
(* Helpers *)

BoundedSeq(S) == UNION {[1..n -> S] : n \in 0..MaxLen}

\* A sequence changes value at most once (consists of at most two runs).
TwoValueMono(s) ==
    \A i, j \in 1..(Len(s) - 1) :
        (s[i] # s[i+1] /\ s[j] # s[j+1]) => i = j

-----------------------------------------------------------------------------
(* Type and state constraints *)

TypeOK ==
    /\ sent \in Data
    /\ rcvd \in Data
    /\ sBit \in Bits
    /\ sAck \in Bits
    /\ rBit \in Bits
    /\ msgC \in BoundedSeq(Bits \X Data)
    /\ ackC \in BoundedSeq(Bits)

-----------------------------------------------------------------------------
(* Initial state *)

Init ==
    /\ sent \in Data
    /\ rcvd = sent
    /\ sBit = 0
    /\ sAck = 0
    /\ rBit = 0
    /\ msgC = << >>
    /\ ackC = << >>

-----------------------------------------------------------------------------
(* Actions *)

\* Sender: previous message acknowledged, so produce a new one and enqueue it.
SndNewValue(d) ==
    /\ sAck = sBit
    /\ Len(msgC) < MaxLen
    /\ sent' = d
    /\ sBit' = 1 - sBit
    /\ msgC' = Append(msgC, <<1 - sBit, d>>)
    /\ UNCHANGED <<sAck, rcvd, rBit, ackC>>

\* Sender: current message not yet acknowledged, so (re)enqueue it.
ReSndMsg ==
    /\ sAck # sBit
    /\ Len(msgC) < MaxLen
    /\ msgC' = Append(msgC, <<sBit, sent>>)
    /\ UNCHANGED <<sent, sBit, sAck, rcvd, rBit, ackC>>

\* Receiver: dequeue the head of the message channel.
RcvMsg ==
    /\ msgC # << >>
    /\ msgC' = Tail(msgC)
    /\ rBit' = Head(msgC)[1]
    /\ rcvd' = Head(msgC)[2]
    /\ UNCHANGED <<sent, sBit, sAck, ackC>>

\* Receiver: enqueue an acknowledgement carrying its current bit.
SndAck ==
    /\ Len(ackC) < MaxLen
    /\ ackC' = Append(ackC, rBit)
    /\ UNCHANGED <<sent, sBit, sAck, rcvd, rBit, msgC>>

\* Sender: dequeue the head of the acknowledgement channel.
RcvAck ==
    /\ ackC # << >>
    /\ ackC' = Tail(ackC)
    /\ sAck' = Head(ackC)
    /\ UNCHANGED <<sent, sBit, rcvd, rBit, msgC>>

SndNew == \E d \in Data : SndNewValue(d)

Next ==
    \/ SndNew
    \/ ReSndMsg
    \/ RcvMsg
    \/ SndAck
    \/ RcvAck

-----------------------------------------------------------------------------
(* Fairness and specification *)

Fairness ==
    /\ WF_vars(SndNew)
    /\ WF_vars(ReSndMsg)
    /\ WF_vars(RcvMsg)
    /\ WF_vars(SndAck)
    /\ WF_vars(RcvAck)

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Properties *)

\* Safety: a matching bit at the head of the ack channel implies agreement.
Safety ==
    (ackC # << >> /\ Head(ackC) = sBit) => (sent = rcvd)

\* Structural consistency: both channels consist of at most two runs.
ChannelsMono ==
    /\ TwoValueMono(msgC)
    /\ TwoValueMono(ackC)

Inv == TypeOK /\ Safety /\ ChannelsMono

\* Liveness: every outstanding message is eventually acknowledged,
\* and the receiver eventually obtains it.
Liveness ==
    /\ (sAck # sBit) ~> (sAck = sBit)
    /\ (rBit # sBit) ~> (rBit = sBit)

THEOREM Spec => []Inv
THEOREM Spec => Liveness
=============================================================================