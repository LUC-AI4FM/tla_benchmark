---------------------------- MODULE AlternatingBitProtocol ----------------------------
EXTENDS Naturals, Sequences

(***************************************************************************)
(* Abstract specification: messages are records [data |-> d, bit |-> b]  *)
(***************************************************************************)
------------------------------ MODULE AbstractABP ------------------------------
EXTENDS Naturals, Sequences

CONSTANTS Data, MsgCap, AckCap

ASSUME /\ Data # {}
       /\ MsgCap \in Nat \ {0}
       /\ AckCap \in Nat \ {0}

VARIABLES sData, sBit,      \* sender's current data value and tag bit
          rData, rBit,      \* receiver's last accepted data value and bit
          msgQ,             \* channel sender -> receiver (FIFO, bounded)
          ackQ,             \* channel receiver -> sender (FIFO, bounded)
          sentHist,         \* history: sequence of data values the sender has issued
          delivered         \* history: sequence of data values the receiver accepted

vars == <<sData, sBit, rData, rBit, msgQ, ackQ, sentHist, delivered>>

Bits == {0, 1}
Msg  == [data : Data, bit : Bits]

RemoveAt(s, i) == [j \in 1..(Len(s) - 1) |-> IF j < i THEN s[j] ELSE s[j + 1]]

TypeOK ==
    /\ sData \in Data /\ sBit \in Bits
    /\ rData \in Data /\ rBit \in Bits
    /\ msgQ \in Seq(Msg)
    /\ ackQ \in Seq(Bits)
    /\ sentHist \in Seq(Data)
    /\ delivered \in Seq(Data)

Init ==
    /\ sData \in Data
    /\ sBit = 0
    /\ rData = sData
    /\ rBit = 0
    /\ msgQ = << >>
    /\ ackQ = << >>
    /\ sentHist = << sData >>
    /\ delivered = << sData >>

\* Sender (re)transmits its current data value paired with its bit.
SndMsg ==
    /\ Len(msgQ) < MsgCap
    /\ msgQ' = Append(msgQ, [data |-> sData, bit |-> sBit])
    /\ UNCHANGED <<sData, sBit, rData, rBit, ackQ, sentHist, delivered>>

\* Receiver takes the head message; accepts it only if its bit differs
\* from the last accepted bit.
RcvMsg ==
    /\ msgQ # << >>
    /\ msgQ' = Tail(msgQ)
    /\ IF Head(msgQ).bit # rBit
         THEN /\ rData' = Head(msgQ).data
              /\ rBit' = Head(msgQ).bit
              /\ delivered' = Append(delivered, Head(msgQ).data)
         ELSE UNCHANGED <<rData, rBit, delivered>>
    /\ UNCHANGED <<sData, sBit, ackQ, sentHist>>

\* Receiver of a fresh (not-yet-accepted) message: used for fairness.
RcvFreshMsg == /\ msgQ # << >>
               /\ Head(msgQ).bit # rBit
               /\ RcvMsg

\* Receiver sends a one-bit acknowledgment carrying its last accepted bit.
SndAck ==
    /\ Len(ackQ) < AckCap
    /\ ackQ' = Append(ackQ, rBit)
    /\ UNCHANGED <<sData, sBit, rData, rBit, msgQ, sentHist, delivered>>

\* Sender takes the head ack; if it matches its bit the current data has
\* been received, so the sender chooses a new data value and flips its bit.
RcvAck ==
    /\ ackQ # << >>
    /\ ackQ' = Tail(ackQ)
    /\ IF Head(ackQ) = sBit
         THEN \E d \in Data :
                 /\ sData' = d
                 /\ sBit' = 1 - sBit
                 /\ sentHist' = Append(sentHist, d)
         ELSE UNCHANGED <<sData, sBit, sentHist>>
    /\ UNCHANGED <<rData, rBit, msgQ, delivered>>

RcvFreshAck == /\ ackQ # << >>
               /\ Head(ackQ) = sBit
               /\ RcvAck

\* Lossy channels: any buffered element may be lost (never corrupted,
\* order of remaining elements preserved).
LoseMsg ==
    /\ \E i \in 1..Len(msgQ) : msgQ' = RemoveAt(msgQ, i)
    /\ UNCHANGED <<sData, sBit, rData, rBit, ackQ, sentHist, delivered>>

LoseAck ==
    /\ \E i \in 1..Len(ackQ) : ackQ' = RemoveAt(ackQ, i)
    /\ UNCHANGED <<sData, sBit, rData, rBit, msgQ, sentHist, delivered>>

Next == \/ SndMsg \/ RcvMsg \/ SndAck \/ RcvAck \/ LoseMsg \/ LoseAck

Fairness ==
    /\ WF_vars(SndMsg)
    /\ WF_vars(SndAck)
    /\ WF_vars(RcvMsg)
    /\ WF_vars(RcvAck)
    /\ SF_vars(RcvFreshMsg)
    /\ SF_vars(RcvFreshAck)

Spec == Init /\ [][Next]_vars /\ Fairness

---------------------------------------------------------------------------
(* Safety / invariance                                                     *)

ChannelBounds == Len(msgQ) <= MsgCap /\ Len(ackQ) <= AckCap

\* Receiver's deliveries are exactly a prefix of what the sender issued:
\* no spurious duplicates or invented data.
NoSpuriousDuplicates ==
    /\ Len(delivered) <= Len(sentHist)
    /\ Len(sentHist) <= Len(delivered) + 1
    /\ \A i \in 1..Len(delivered) : delivered[i] = sentHist[i]

\* Bits agree exactly when the latest data has been received/acknowledgeable.
BitsAgreement ==
    /\ (sBit = rBit) <=> (Len(delivered) = Len(sentHist))
    /\ (sBit = rBit) => (rData = sData)

\* Auxiliary inductive facts about channel contents.
FreshMsgsAreCurrent ==
    \A i \in 1..Len(msgQ) :
        msgQ[i].bit # rBit => (msgQ[i].bit = sBit /\ msgQ[i].data = sData)

AcksSound ==
    \A i \in 1..Len(ackQ) : ackQ[i] = sBit => rBit = sBit

Safety == TypeOK /\ ChannelBounds /\ NoSpuriousDuplicates /\ BitsAgreement
          /\ FreshMsgsAreCurrent /\ AcksSound

---------------------------------------------------------------------------
(* Liveness                                                                *)

\* Every message the sender keeps (re)sending is eventually acknowledged
\* and superseded by a later message.
MsgEventuallyHandled ==
    \A d \in Data, b \in Bits :
        (sData = d /\ sBit = b) ~> (sBit # b)

\* Receiver eventually catches up with the sender.
ReceiverProgress == (sBit # rBit) ~> (sBit = rBit)

Liveness == MsgEventuallyHandled /\ ReceiverProgress

THEOREM Spec => []Safety
THEOREM Spec => Liveness
================================================================================