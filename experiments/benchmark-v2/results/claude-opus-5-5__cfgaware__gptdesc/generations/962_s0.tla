---------------------------- MODULE ABCorrectness ----------------------------
EXTENDS Naturals

CONSTANT Data

VARIABLES sBit, sAck, rBit, sent, rcvd

abcvars == <<sBit, sAck, rBit, sent, rcvd>>

-----------------------------------------------------------------------------
TypeInv == /\ sBit \in {0, 1}
           /\ sAck \in {0, 1}
           /\ rBit \in {0, 1}
           /\ sent \in Data
           /\ rcvd \in Data

ABCInit == /\ sBit \in {0, 1}
           /\ sAck = sBit
           /\ rBit = sBit
           /\ sent \in Data
           /\ rcvd \in Data

SndNewValue(d) == /\ sAck = sBit
                  /\ sent' = d
                  /\ sBit' = 1 - sBit
                  /\ UNCHANGED <<sAck, rBit, rcvd>>

RcvMsg == /\ rBit # sBit
          /\ rBit' = sBit
          /\ rcvd' = sent
          /\ UNCHANGED <<sBit, sAck, sent>>

RcvAck == /\ rBit # sAck
          /\ sAck' = rBit
          /\ UNCHANGED <<sBit, rBit, sent, rcvd>>

ABCNext == \/ \E d \in Data : SndNewValue(d)
           \/ RcvMsg
           \/ RcvAck

ABCFairness == WF_abcvars(RcvMsg) /\ WF_abcvars(RcvAck)

ABCSpec == ABCInit /\ [][ABCNext]_abcvars /\ ABCFairness

-----------------------------------------------------------------------------
ABCLiveness == []<>(sBit # sAck)

THEOREM ABCSpec => []TypeInv
=============================================================================