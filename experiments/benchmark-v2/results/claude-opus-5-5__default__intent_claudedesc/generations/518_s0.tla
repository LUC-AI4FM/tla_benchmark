------------------------------ MODULE AlternatingBit ------------------------------
EXTENDS Naturals, Sequences

CONSTANT Data

ASSUME Data # {}

VARIABLES
    msgQ,   \* data channel (sender -> receiver): sequence of <<bit, data>>
    ackQ,   \* ack channel (receiver -> sender): sequence of bits
    sBit,   \* sender's current sequence bit
    sAck,   \* last ack bit received by the sender
    rBit,   \* sequence bit of the last message accepted by the receiver
    sent,   \* data item the sender is currently transmitting
    rcvd    \* data item most recently accepted by the receiver

vars == <<msgQ, ackQ, sBit, sAck, rBit, sent, rcvd>>

Bits == {0, 1}

Msgs == Bits \X Data

\* Remove the i-th element of a sequence
Remove(i, seq) == SubSeq(seq, 1, i - 1) \o SubSeq(seq, i + 1, Len(seq))

TypeOK ==
    /\ msgQ \in Seq(Msgs)
    /\ ackQ \in Seq(Bits)
    /\ sBit \in Bits
    /\ sAck \in Bits
    /\ rBit \in Bits
    /\ sent \in Data
    /\ rcvd \in Data

Init ==
    /\ msgQ = << >>
    /\ ackQ = << >>
    /\ sBit \in Bits
    /\ sAck = sBit
    /\ rBit = sBit
    /\ sent \in Data
    /\ rcvd \in Data

-----------------------------------------------------------------------------------
\* Sender actions

\* Sender has received a matching ack: choose next data item and flip the bit
SndNewValue(d) ==
    /\ sAck = sBit
    /\ sent' = d
    /\ sBit' = 1 - sBit
    /\ UNCHANGED <<msgQ, ackQ, sAck, rBit, rcvd>>

\* Sender (re)transmits the current message while awaiting a matching ack
ReSndMsg ==
    /\ sAck # sBit
    /\ msgQ' = Append(msgQ, <<sBit, sent>>)
    /\ UNCHANGED <<ackQ, sBit, sAck, rBit, sent, rcvd>>

\* Sender receives an acknowledgment
RcvAck ==
    /\ ackQ # << >>
    /\ sAck' = Head(ackQ)
    /\ ackQ' = Tail(ackQ)
    /\ UNCHANGED <<msgQ, sBit, rBit, sent, rcvd>>

-----------------------------------------------------------------------------------
\* Receiver actions

\* Receiver takes a message; accepts data only if its bit differs from the last
\* accepted bit
RcvMsg ==
    /\ msgQ # << >>
    /\ msgQ' = Tail(msgQ)
    /\ IF Head(msgQ)[1] # rBit
          THEN /\ rBit' = Head(msgQ)[1]
               /\ rcvd' = Head(msgQ)[2]
          ELSE UNCHANGED <<rBit, rcvd>>
    /\ UNCHANGED <<ackQ, sBit, sAck, sent>>

\* Receiver sends an ack carrying the bit of the most recently accepted message
SndAck ==
    /\ ackQ' = Append(ackQ, rBit)
    /\ UNCHANGED <<msgQ, sBit, sAck, rBit, sent, rcvd>>

-----------------------------------------------------------------------------------
\* Unreliable channels: any message in transit may be lost

LoseMsg ==
    /\ \E i \in 1..Len(msgQ) : msgQ' = Remove(i, msgQ)
    /\ UNCHANGED <<ackQ, sBit, sAck, rBit, sent, rcvd>>

LoseAck ==
    /\ \E i \in 1..Len(ackQ) : ackQ' = Remove(i, ackQ)
    /\ UNCHANGED <<msgQ, sBit, sAck, rBit, sent, rcvd>>

-----------------------------------------------------------------------------------

Next ==
    \/ \E d \in Data : SndNewValue(d)
    \/ ReSndMsg
    \/ RcvAck
    \/ RcvMsg
    \/ SndAck
    \/ LoseMsg
    \/ LoseAck

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------------
\* Safety properties

\* If the receiver has accepted the sender's current bit, it holds the sender's
\* current data
DataConsistent ==
    (rBit = sBit) => (rcvd = sent)

\* If the sender has received a matching ack, the receiver has accepted the
\* current message (sender and receiver are synchronized)
BitSynchronized ==
    (sAck = sBit) => (rBit = sBit /\ rcvd = sent)

\* Any message in transit carrying the current bit carries the current data
ChannelConsistent ==
    \A i \in 1..Len(msgQ) : (msgQ[i][1] = sBit) => (msgQ[i][2] = sent)

\* Any ack in transit carrying the sender's current bit implies the receiver
\* has accepted the current message
AckConsistent ==
    \A i \in 1..Len(ackQ) : (ackQ[i] = sBit) => (rBit = sBit)

Inv ==
    /\ TypeOK
    /\ DataConsistent
    /\ BitSynchronized
    /\ ChannelConsistent
    /\ AckConsistent

THEOREM Spec => []Inv
===================================================================================