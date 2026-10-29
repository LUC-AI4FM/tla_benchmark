---------------------------- MODULE AlternatingBit ----------------------------
EXTENDS Naturals, Sequences

CONSTANT Data

VARIABLES msgQ,   \* queue of <<bit, data>> messages from sender to receiver
          ackQ,   \* queue of bit acknowledgments from receiver to sender
          sBit,   \* sender's current control bit
          sAck,   \* last acknowledgment bit received by the sender
          rBit,   \* last bit received by the receiver
          sent,   \* last data value sent by the sender
          rcvd    \* last data value received by the receiver

vars == <<msgQ, ackQ, sBit, sAck, rBit, sent, rcvd>>

-----------------------------------------------------------------------------

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

-----------------------------------------------------------------------------

\* Sender sends a new data value once the previous one has been acknowledged.
SndNewValue(d) == /\ sAck = sBit
                  /\ sent' = d
                  /\ sBit' = 1 - sBit
                  /\ msgQ' = Append(msgQ, <<sBit', d>>)
                  /\ UNCHANGED <<ackQ, sAck, rBit, rcvd>>

\* Sender retransmits the current message while the ack does not match.
ReSndMsg == /\ sAck # sBit
            /\ msgQ' = Append(msgQ, <<sBit, sent>>)
            /\ UNCHANGED <<ackQ, sBit, sAck, rBit, sent, rcvd>>

\* Receiver takes a message from the message queue.
RcvMsg == /\ msgQ # << >>
          /\ msgQ' = Tail(msgQ)
          /\ rBit' = Head(msgQ)[1]
          /\ rcvd' = Head(msgQ)[2]
          /\ UNCHANGED <<ackQ, sBit, sAck, sent>>

\* Receiver sends an acknowledgment carrying its last received bit.
SndAck == /\ ackQ' = Append(ackQ, rBit)
          /\ UNCHANGED <<msgQ, sBit, sAck, rBit, sent, rcvd>>

\* Sender takes an acknowledgment from the ack queue.
RcvAck == /\ ackQ # << >>
          /\ ackQ' = Tail(ackQ)
          /\ sAck' = Head(ackQ)
          /\ UNCHANGED <<msgQ, sBit, rBit, sent, rcvd>>

\* Remove one arbitrary element from queue q.
Lose(q) == /\ q # << >>
           /\ \E i \in 1..Len(q) :
                 q' = [j \in 1..(Len(q) - 1) |-> IF j < i THEN q[j] ELSE q[j + 1]]

LoseMsg == /\ Lose(msgQ)
           /\ UNCHANGED <<ackQ, sBit, sAck, rBit, sent, rcvd>>

LoseAck == /\ Lose(ackQ)
           /\ UNCHANGED <<msgQ, sBit, sAck, rBit, sent, rcvd>>

ABNext == \/ \E d \in Data : SndNewValue(d)
          \/ ReSndMsg
          \/ RcvMsg
          \/ SndAck
          \/ RcvAck
          \/ LoseMsg
          \/ LoseAck

-----------------------------------------------------------------------------

ABFairness == /\ WF_vars(ReSndMsg)
              /\ WF_vars(SndAck)
              /\ SF_vars(RcvMsg)
              /\ SF_vars(RcvAck)

ABSpec == ABInit /\ [][ABNext]_vars /\ ABFairness

Spec == ABSpec

-----------------------------------------------------------------------------

THEOREM ABSpec => []ABTypeInv

=============================================================================