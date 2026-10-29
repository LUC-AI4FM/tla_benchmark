---------------------------- MODULE ABCorrectness ----------------------------
EXTENDS Naturals

CONSTANT Data

VARIABLES sBit, sAck, rBit, sent, rcvd

vars == << sBit, sAck, rBit, sent, rcvd >>

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

CSnd == /\ sAck = sBit
        /\ sent' \in Data
        /\ sBit' = 1 - sBit
        /\ UNCHANGED << sAck, rBit, rcvd >>

CRcv == /\ rBit # sBit
        /\ rBit' = sBit
        /\ rcvd' = sent
        /\ UNCHANGED << sBit, sAck, sent >>

CAck == /\ sAck # rBit
        /\ sAck' = rBit
        /\ UNCHANGED << sBit, rBit, sent, rcvd >>

CNext == CSnd \/ CRcv \/ CAck

ABCSpec == /\ ABCInit
           /\ [][CNext]_vars
           /\ WF_vars(CRcv)
           /\ WF_vars(CAck)
=============================================================================