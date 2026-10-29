---------------------------- MODULE ABE ----------------------------
EXTENDS Naturals, Sequences

CONSTANT Data

ConstData == {"Fred", "Mary", "Ted"}

VARIABLES msgQ,   \* channel sender -> receiver: sequence of <<data, bit>>
          ackQ,   \* channel receiver -> sender: sequence of bits
          sBit,   \* sender's current bit
          sAck,   \* last ack bit received by sender
          rBit,   \* receiver's current bit
          sent,   \* value currently being sent
          rcvd,   \* value last received by receiver
          envQ    \* pending values produced by the environment

vars == <<msgQ, ackQ, sBit, sAck, rBit, sent, rcvd, envQ>>

Bits == {0, 1}

Msgs == Data \X Bits

Remove(i, seq) ==
  [j \in 1..(Len(seq) - 1) |-> IF j < i THEN seq[j] ELSE seq[j + 1]]

-----------------------------------------------------------------------------
ABE_TypeOK ==
  /\ msgQ \in Seq(Msgs)
  /\ ackQ \in Seq(Bits)
  /\ sBit \in Bits
  /\ sAck \in Bits
  /\ rBit \in Bits
  /\ sent \in Data
  /\ rcvd \in Data
  /\ envQ \in Seq(Data)

Init ==
  /\ msgQ = << >>
  /\ ackQ = << >>
  /\ sBit \in Bits
  /\ sAck = sBit
  /\ rBit = sBit
  /\ sent \in Data
  /\ rcvd = sent
  /\ envQ = << >>

\* Environment produces a new value to be transmitted
EnvProduce ==
  /\ \E d \in Data : envQ' = Append(envQ, d)
  /\ UNCHANGED <<msgQ, ackQ, sBit, sAck, rBit, sent, rcvd>>

\* Sender takes the next pending value once the previous one is acknowledged
SndNewValue ==
  /\ sAck = sBit
  /\ envQ # << >>
  /\ sent' = Head(envQ)
  /\ envQ' = Tail(envQ)
  /\ sBit' = 1 - sBit
  /\ msgQ' = Append(msgQ, <<Head(envQ), 1 - sBit>>)
  /\ UNCHANGED <<ackQ, sAck, rBit, rcvd>>

\* Sender (re)transmits the current message
ReSndMsg ==
  /\ sAck # sBit
  /\ msgQ' = Append(msgQ, <<sent, sBit>>)
  /\ UNCHANGED <<ackQ, sBit, sAck, rBit, sent, rcvd, envQ>>

\* Receiver receives a message
RcvMsg ==
  /\ msgQ # << >>
  /\ msgQ' = Tail(msgQ)
  /\ rBit' = Head(msgQ)[2]
  /\ rcvd' = Head(msgQ)[1]
  /\ UNCHANGED <<ackQ, sBit, sAck, sent, envQ>>

\* Receiver sends an acknowledgment
SndAck ==
  /\ ackQ' = Append(ackQ, rBit)
  /\ UNCHANGED <<msgQ, sBit, sAck, rBit, sent, rcvd, envQ>>

\* Sender receives an acknowledgment
RcvAck ==
  /\ ackQ # << >>
  /\ ackQ' = Tail(ackQ)
  /\ sAck' = Head(ackQ)
  /\ UNCHANGED <<msgQ, sBit, rBit, sent, rcvd, envQ>>

\* Unreliable channels: messages may be lost
LoseMsg ==
  /\ \E i \in 1..Len(msgQ) : msgQ' = Remove(i, msgQ)
  /\ UNCHANGED <<ackQ, sBit, sAck, rBit, sent, rcvd, envQ>>

LoseAck ==
  /\ \E i \in 1..Len(ackQ) : ackQ' = Remove(i, ackQ)
  /\ UNCHANGED <<msgQ, sBit, sAck, rBit, sent, rcvd, envQ>>

Next ==
  \/ EnvProduce
  \/ SndNewValue
  \/ ReSndMsg
  \/ RcvMsg
  \/ SndAck
  \/ RcvAck
  \/ LoseMsg
  \/ LoseAck

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
\* Bounding constraint for model checking
StateConstraint ==
  /\ Len(msgQ) <= 3
  /\ Len(ackQ) <= 3
  /\ Len(envQ) <= 2

\* Consistency: when sender has an ack matching its bit, both sides agree
Consistency ==
  (sAck = sBit) => (sent = rcvd /\ rBit = sBit)

\* Messages in transit contain at most two distinct values
TwoValues ==
  LET MsgSet == {msgQ[i] : i \in 1..Len(msgQ)}
      AckSet == {ackQ[i] : i \in 1..Len(ackQ)}
  IN  /\ \A m1, m2, m3 \in MsgSet : m1 = m2 \/ m1 = m3 \/ m2 = m3
      /\ \A a1, a2, a3 \in AckSet : a1 = a2 \/ a1 = a3 \/ a2 = a3

-----------------------------------------------------------------------------
\* High-level ABP-with-environment specification, under a refinement mapping
AVarBar == <<sent, sBit>>
BVarBar == <<rcvd, rBit>>

ABEInit ==
  /\ AVarBar \in Data \X Bits
  /\ BVarBar = AVarBar
  /\ envQ = << >>

ABE_A ==
  /\ AVarBar = BVarBar
  /\ envQ # << >>
  /\ AVarBar' = <<Head(envQ), 1 - AVarBar[2]>>
  /\ envQ' = Tail(envQ)
  /\ UNCHANGED BVarBar

ABE_B ==
  /\ AVarBar # BVarBar
  /\ BVarBar' = AVarBar
  /\ UNCHANGED <<AVarBar, envQ>>

ABE_Env ==
  /\ \E d \in Data : envQ' = Append(envQ, d)
  /\ UNCHANGED <<AVarBar, BVarBar>>

ABENext == ABE_A \/ ABE_B \/ ABE_Env

ABESpecProperty == ABEInit /\ [][ABENext]_<<AVarBar, BVarBar, envQ>>

=============================================================================