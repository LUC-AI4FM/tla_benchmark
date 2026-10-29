---------------------------- MODULE ABCorrectness ----------------------------
EXTENDS Naturals

CONSTANTS Data

VARIABLES sBit, sAck, rBit, sent, rcvd

vars == <<sBit, sAck, rBit, sent, rcvd>>

TypeInv ==
    /\ sBit \in {0, 1}
    /\ sAck \in {0, 1}
    /\ rBit \in {0, 1}
    /\ sent \in Data
    /\ rcvd \in Data

ABCInit ==
    /\ sBit \in {0, 1}
    /\ sAck = sBit
    /\ rBit = sBit
    /\ sent \in Data
    /\ rcvd \in Data

CSndNewValue(d) ==
    /\ sAck = sBit
    /\ sent' = d
    /\ sBit' = 1 - sBit
    /\ UNCHANGED <<sAck, rBit, rcvd>>

CRcvMsg ==
    /\ rBit # sBit
    /\ rBit' = sBit
    /\ rcvd' = sent
    /\ UNCHANGED <<sBit, sAck, sent>>

CRcvAck ==
    /\ rBit # sAck
    /\ sAck' = rBit
    /\ UNCHANGED <<sBit, rBit, sent, rcvd>>

ABCNext ==
    \/ \E d \in Data : CSndNewValue(d)
    \/ CRcvMsg
    \/ CRcvAck

ABCFairness == WF_vars(CRcvMsg) /\ WF_vars(CRcvAck)

ABCSpec == ABCInit /\ [][ABCNext]_vars /\ ABCFairness

THEOREM ABCSpec => []TypeInv
=============================================================================