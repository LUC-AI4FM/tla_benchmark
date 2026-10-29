---------------------------- MODULE ABCorrectness ----------------------------
EXTENDS Integers

CONSTANTS Data

VARIABLES sBit, sAck, rBit, sent, rcvd

cvars == << sBit, sAck, rBit, sent, rcvd >>

-----------------------------------------------------------------------------

TypeOK == /\ sBit \in {0, 1}
          /\ sAck \in {0, 1}
          /\ rBit \in {0, 1}
          /\ sent \in Data
          /\ rcvd \in Data

ABCInit == /\ sBit \in {0, 1}
           /\ sAck = sBit
           /\ rBit = sBit
           /\ sent \in Data
           /\ rcvd \in Data

CSndNewValue(d) == /\ sAck = sBit
                   /\ sent' = d
                   /\ sBit' = 1 - sBit
                   /\ UNCHANGED << sAck, rBit, rcvd >>

CRcvMsg == /\ rBit # sBit
           /\ rBit' = sBit
           /\ rcvd' = sent
           /\ UNCHANGED << sBit, sAck, sent >>

CRcvAck == /\ rBit # sAck
           /\ sAck' = rBit
           /\ UNCHANGED << sBit, rBit, sent, rcvd >>

ABCNext == \/ \E d \in Data : CSndNewValue(d)
           \/ CRcvMsg
           \/ CRcvAck

ABCFairness == WF_cvars(CRcvMsg) /\ WF_cvars(CRcvAck)

Init == ABCInit

Next == ABCNext

ABCSpec == ABCInit /\ [][ABCNext]_cvars /\ ABCFairness

Spec == ABCSpec

-----------------------------------------------------------------------------

Inv == (rBit = sBit) => (rcvd = sent)

SyncLiveness == []<>(sBit # sAck)

THEOREM ABCSpec => []TypeOK
THEOREM ABCSpec => []Inv
=============================================================================