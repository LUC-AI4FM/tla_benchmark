---------------------------- MODULE AlternatingBit ----------------------------
EXTENDS Naturals, Sequences

CONSTANT Data

VARIABLES msgQ, ackQ, sBit, sAck, rBit, sent, rcvd

vars == <<msgQ, ackQ, sBit, sAck, rBit, sent, rcvd>>

TypeOK ==
  /\ msgQ \in Seq({0, 1} \X Data)
  /\ ackQ \in Seq({0, 1})
  /\ sBit \in {0, 1}
  /\ sAck \in {0, 1}
  /\ rBit \in {0, 1}
  /\ sent \in Data
  /\ rcvd \in Data

Init ==
  /\ msgQ = << >>
  /\ ackQ = << >>
  /\ sBit \in {0, 1}
  /\ sAck = sBit
  /\ rBit = sBit
  /\ sent \in Data
  /\ rcvd \in Data

\* Sender sends a new data value once the current bit has been acknowledged
SndNewValue(d) ==
  /\ sAck = sBit
  /\ sent' = d
  /\ sBit' = 1 - sBit
  /\ msgQ' = Append(msgQ, <<1 - sBit, d>>)
  /\ UNCHANGED <<ackQ, sAck, rBit, rcvd>>

\* Sender retransmits the current message while ack does not match the bit
ReSndMsg ==
  /\ sAck # sBit
  /\ msgQ' = Append(msgQ, <<sBit, sent>>)
  /\ UNCHANGED <<ackQ, sBit, sAck, rBit, sent, rcvd>>

\* Receiver receives a message, recording its bit and data value
RcvMsg ==
  /\ msgQ # << >>
  /\ msgQ' = Tail(msgQ)
  /\ rBit' = Head(msgQ)[1]
  /\ rcvd' = Head(msgQ)[2]
  /\ UNCHANGED <<ackQ, sBit, sAck, sent>>

\* Receiver sends an acknowledgment carrying the last received bit
SndAck ==
  /\ ackQ' = Append(ackQ, rBit)
  /\ UNCHANGED <<msgQ, sBit, sAck, rBit, sent, rcvd>>

\* Sender receives an acknowledgment
RcvAck ==
  /\ ackQ # << >>
  /\ ackQ' = Tail(ackQ)
  /\ sAck' = Head(ackQ)
  /\ UNCHANGED <<msgQ, sBit, rBit, sent, rcvd>>

\* Remove exactly one element from a nonempty queue
Lose(q) ==
  /\ q # << >>
  /\ \E i \in 1..Len(q) :
       q' = [j \in 1..(Len(q) - 1) |-> IF j < i THEN q[j] ELSE q[j + 1]]

LoseMsg ==
  /\ Lose(msgQ)
  /\ UNCHANGED <<ackQ, sBit, sAck, rBit, sent, rcvd>>

LoseAck ==
  /\ Lose(ackQ)
  /\ UNCHANGED <<msgQ, sBit, sAck, rBit, sent, rcvd>>

Next ==
  \/ \E d \in Data : SndNewValue(d)
  \/ ReSndMsg
  \/ RcvMsg
  \/ SndAck
  \/ RcvAck
  \/ LoseMsg
  \/ LoseAck

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(ReSndMsg)
  /\ WF_vars(SndAck)
  /\ SF_vars(RcvMsg)
  /\ SF_vars(RcvAck)

THEOREM Spec => []TypeOK
=============================================================================