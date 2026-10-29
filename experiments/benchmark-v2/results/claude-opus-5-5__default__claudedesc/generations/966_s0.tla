------------------------------ MODULE MCAlternatingBit ------------------------------
EXTENDS Naturals, Sequences, TLC

CONSTANTS Data, msgQLen, ackQLen

VARIABLES msgQ, ackQ, sBit, sAck, rBit, sent, rcvd

abvars == <<msgQ, ackQ, sBit, sAck, rBit, sent, rcvd>>

-----------------------------------------------------------------------------
(* Base Alternating Bit Protocol (AlternatingBit)                          *)
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

SndNewValue(d) == /\ sAck = sBit
                  /\ sent' = d
                  /\ sBit' = 1 - sBit
                  /\ msgQ' = Append(msgQ, <<1 - sBit, d>>)
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

RemoveAt(s, i) == [j \in 1..(Len(s) - 1) |-> IF j < i THEN s[j] ELSE s[j + 1]]

LoseMsg == /\ msgQ # << >>
           /\ \E i \in 1..Len(msgQ) : msgQ' = RemoveAt(msgQ, i)
           /\ UNCHANGED <<ackQ, sBit, sAck, rBit, sent, rcvd>>

LoseAck == /\ ackQ # << >>
           /\ \E i \in 1..Len(ackQ) : ackQ' = RemoveAt(ackQ, i)
           /\ UNCHANGED <<msgQ, sBit, sAck, rBit, sent, rcvd>>

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
(* Correctness conditions (ABCorrectness)                                  *)
-----------------------------------------------------------------------------

cvars == <<sBit, sAck, rBit, sent, rcvd>>

CInit == /\ sBit \in {0, 1}
         /\ sAck = sBit
         /\ rBit = sBit
         /\ sent \in Data
         /\ rcvd \in Data

CSndNewValue(d) == /\ sAck = sBit
                   /\ sent' = d
                   /\ sBit' = 1 - sBit
                   /\ UNCHANGED <<sAck, rBit, rcvd>>

CRcvMsg == /\ rBit # sBit
           /\ rBit' = sBit
           /\ rcvd' = sent
           /\ UNCHANGED <<sBit, sAck, sent>>

CRcvAck == /\ rBit # sAck
           /\ sAck' = rBit
           /\ UNCHANGED <<sBit, rBit, sent, rcvd>>

CNext == \/ \E d \in Data : CSndNewValue(d)
         \/ CRcvMsg
         \/ CRcvAck

ABCSpec == CInit /\ [][CNext]_cvars /\ WF_cvars(CRcvMsg) /\ WF_cvars(CRcvAck)

-----------------------------------------------------------------------------
(* Model-checking configuration                                            *)
-----------------------------------------------------------------------------

Init == ABInit
Next == ABNext
Spec == ABSpec

SeqConstraint == /\ Len(msgQ) \leq msgQLen
                 /\ Len(ackQ) \leq ackQLen

SentLeadsToRcvd == \A d \in Data : ((sent = d) /\ (sBit # sAck)) ~> (rcvd = d)

THEOREM Spec => []ABTypeInv
THEOREM Spec => ABCSpec
THEOREM Spec => SentLeadsToRcvd
=============================================================================