--------------------------- MODULE AlternatingBit ---------------------------
EXTENDS Naturals, Sequences

CONSTANT Data

VARIABLES msgQ,   \* data channel: sequence of <<bit, data>> messages
          ackQ,   \* ack channel: sequence of bits
          sBit,   \* sender's current sequence bit
          sAck,   \* last ack bit received by the sender
          rBit,   \* last sequence bit received by the receiver
          sent,   \* last value sent by the sender
          rcvd    \* last value received by the receiver

abvars == <<msgQ, ackQ, sBit, sAck, rBit, sent, rcvd>>

ABInit == /\ msgQ = << >>
          /\ ackQ = << >>
          /\ sBit \in {0, 1}
          /\ sAck = sBit
          /\ rBit = sBit
          /\ sent \in Data
          /\ rcvd \in Data

ABTypeInv == /\ msgQ \in Seq({0, 1} \X Data)
             /\ ackQ \in Seq({0, 1})
             /\ sBit \in {0, 1}
             /\ sAck \in {0, 1}
             /\ rBit \in {0, 1}
             /\ sent \in Data
             /\ rcvd \in Data

SndNewValue(d) == /\ sAck = sBit
                  /\ sent' = d
                  /\ sBit' = 1 - sBit
                  /\ msgQ' = Append(msgQ, <<sBit', d>>)
                  /\ UNCHANGED <<ackQ, sAck, rBit, rcvd>>

ReSndMsg == /\ sAck # sBit
            /\ msgQ' = Append(msgQ, <<sBit, sent>>)
            /\ UNCHANGED <<ackQ, sBit, sAck, rBit, sent, rcvd>>

RcvMsg == /\ msgQ # << >>
          /\ msgQ' = Tail(msgQ)
          /\ rBit' = Head(msgQ)[1]
          /\ rcvd' = Head(msgQ)[2]
          /\ UNCHANGED <<ackQ, sBit, sAck, sent>>

SndAck == /\ ackQ' = Append(ackQ, rBit)
          /\ UNCHANGED <<msgQ, sBit, sAck, rBit, sent, rcvd>>

RcvAck == /\ ackQ # << >>
          /\ ackQ' = Tail(ackQ)
          /\ sAck' = Head(ackQ)
          /\ UNCHANGED <<msgQ, sBit, rBit, sent, rcvd>>

RemoveAt(c, i) == [j \in 1..(Len(c) - 1) |-> IF j < i THEN c[j] ELSE c[j + 1]]

Lose(c) == /\ c # << >>
           /\ \E i \in 1..Len(c) : c' = RemoveAt(c, i)
           /\ UNCHANGED <<sBit, sAck, rBit, sent, rcvd>>

LoseMsg == Lose(msgQ) /\ UNCHANGED ackQ

LoseAck == Lose(ackQ) /\ UNCHANGED msgQ

ABNext == \/ \E d \in Data : SndNewValue(d)
          \/ ReSndMsg
          \/ RcvMsg
          \/ SndAck
          \/ RcvAck
          \/ LoseMsg
          \/ LoseAck

ABFairness == /\ WF_abvars(ReSndMsg)
              /\ WF_abvars(SndAck)
              /\ SF_abvars(RcvMsg)
              /\ SF_abvars(RcvAck)

ABSpec == ABInit /\ [][ABNext]_abvars /\ ABFairness

-----------------------------------------------------------------------------
\* Reliable delivery: when the receiver's bit matches the sender's bit,
\* the receiver holds exactly the value the sender sent.
ABConsistent == (rBit = sBit) => (rcvd = sent)

\* Every message in the channel carrying the current bit carries the current value.
ABMsgConsistent == \A i \in 1..Len(msgQ) :
                      (msgQ[i][1] = sBit) => (msgQ[i][2] = sent)

\* Liveness: an unacknowledged message is eventually received.
ABDelivery == (sAck # sBit) ~> (rBit = sBit)

THEOREM ABSpec => [](ABTypeInv /\ ABConsistent)
=============================================================================