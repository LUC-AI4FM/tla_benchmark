------------------------------ MODULE AlternatingBit ------------------------------
EXTENDS Naturals, Sequences

CONSTANT Data

VARIABLES msgQ,  \* sequence of <<bit, data>> messages in transit to receiver
          ackQ,  \* sequence of bits (acknowledgments) in transit to sender
          sBit,  \* sender's current bit
          sAck,  \* last acknowledgment bit received by sender
          rBit,  \* receiver's current bit
          sent,  \* last value sent by sender
          rcvd   \* last value received by receiver

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

Lose(q) == /\ q # << >>
           /\ \E i \in 1..Len(q) :
                 q' = [j \in 1..(Len(q) - 1) |-> IF j < i THEN q[j] ELSE q[j + 1]]
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

THEOREM ABSpec => []ABTypeInv
================================================================================