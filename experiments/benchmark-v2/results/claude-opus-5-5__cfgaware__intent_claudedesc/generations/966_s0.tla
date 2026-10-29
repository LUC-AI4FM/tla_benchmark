---------------------------- MODULE AlternatingBit ----------------------------
EXTENDS Naturals, Sequences

CONSTANTS Data, msgQLen, ackQLen

VARIABLES msgQ, ackQ, sBit, sAck, rBit, sent, rcvd

abvars == << msgQ, ackQ, sBit, sAck, rBit, sent, rcvd >>

-----------------------------------------------------------------------------
\* The protocol

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
                  /\ msgQ' = Append(msgQ, << sBit', d >>)
                  /\ UNCHANGED << ackQ, sAck, rBit, rcvd >>

ReSndMsg == /\ sAck # sBit
            /\ msgQ' = Append(msgQ, << sBit, sent >>)
            /\ UNCHANGED << ackQ, sBit, sAck, rBit, sent, rcvd >>

RcvMsg == /\ msgQ # << >>
          /\ msgQ' = Tail(msgQ)
          /\ rBit' = Head(msgQ)[1]
          /\ rcvd' = Head(msgQ)[2]
          /\ UNCHANGED << ackQ, sBit, sAck, sent >>

SndAck == /\ ackQ' = Append(ackQ, rBit)
          /\ UNCHANGED << msgQ, sBit, sAck, rBit, sent, rcvd >>

RcvAck == /\ ackQ # << >>
          /\ ackQ' = Tail(ackQ)
          /\ sAck' = Head(ackQ)
          /\ UNCHANGED << msgQ, sBit, rBit, sent, rcvd >>

Lose(c) == /\ c # << >>
           /\ \E i \in 1..Len(c) :
                 c' = [j \in 1..(Len(c) - 1) |-> IF j < i THEN c[j] ELSE c[j + 1]]
           /\ UNCHANGED << sBit, sAck, rBit, sent, rcvd >>

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
\* Model-checking constraint and liveness property

SeqConstraint == /\ Len(msgQ) \leq msgQLen
                 /\ Len(ackQ) \leq ackQLen

SentLeadsToRcvd == \A v \in Data : (sent = v) /\ (sBit # sAck) ~> (rcvd = v)

-----------------------------------------------------------------------------
\* High-level specification of correct reliable transfer

cvars == << sBit, sAck, rBit, sent, rcvd >>

CInit == /\ sBit \in {0, 1}
         /\ sAck = sBit
         /\ rBit = sBit
         /\ sent \in Data
         /\ rcvd \in Data

CSndNewValue == /\ sAck = sBit
                /\ \E d \in Data : sent' = d
                /\ sBit' = 1 - sBit
                /\ UNCHANGED << sAck, rBit, rcvd >>

CRcvMsg == /\ sBit # rBit
           /\ rcvd' = sent
           /\ rBit' = sBit
           /\ UNCHANGED << sBit, sAck, sent >>

CRcvAck == /\ rBit # sAck
           /\ sAck' = rBit
           /\ UNCHANGED << sBit, rBit, sent, rcvd >>

CNext == CSndNewValue \/ CRcvMsg \/ CRcvAck

ABCSpec == CInit /\ [][CNext]_cvars /\ WF_cvars(CNext)

THEOREM ABSpec => []ABTypeInv
THEOREM ABSpec => ABCSpec
=============================================================================