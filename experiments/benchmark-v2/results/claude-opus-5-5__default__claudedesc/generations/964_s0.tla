--------------------------- MODULE AlternatingBit ---------------------------
EXTENDS Naturals, Sequences

CONSTANTS Data

VARIABLES msgQ,   \* queue of <<bit, data>> messages from sender to receiver
          ackQ,   \* queue of acknowledgment bits from receiver to sender
          sBit,   \* sender's current bit
          sAck,   \* last acknowledgment bit received by the sender
          rBit,   \* receiver's current bit
          sent,   \* most recently sent data value
          rcvd    \* most recently received data value

abvars == <<msgQ, ackQ, sBit, sAck, rBit, sent, rcvd>>

-----------------------------------------------------------------------------

ABTypeInv == /\ msgQ \in Seq({0, 1} \X Data)
             /\ ackQ \in Seq({0, 1})
             /\ sBit \in {0, 1}
             /\ sAck \in {0, 1}
             /\ rBit \in {0, 1}
             /\ sent \in Data
             /\ rcvd \in Data

ABInit == /\ msgQ = << >>
          /\ ackQ = << >>
          /\ sBit \in {0, 1}
          /\ sAck = sBit
          /\ rBit = sBit
          /\ sent \in Data
          /\ rcvd \in Data

-----------------------------------------------------------------------------

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

\* Remove an arbitrary element from a queue
Lose(c) == /\ c # << >>
           /\ \E i \in 1..Len(c) :
                 c' = [j \in 1..(Len(c) - 1) |-> IF j < i THEN c[j]
                                                          ELSE c[j + 1]]
           /\ UNCHANGED <<sBit, sAck, rBit, sent, rcvd>>

LoseMsg == Lose(msgQ) /\ UNCHANGED ackQ

LoseAck == Lose(ackQ) /\ UNCHANGED msgQ

-----------------------------------------------------------------------------

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

THEOREM ABSpec => []ABTypeInv

=============================================================================