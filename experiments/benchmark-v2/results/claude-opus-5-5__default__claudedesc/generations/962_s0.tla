---------------------------- MODULE ABCorrectness ----------------------------
EXTENDS Naturals

CONSTANTS Data

VARIABLES sBit, sAck, rBit, sent, rcvd

vars == << sBit, sAck, rBit, sent, rcvd >>

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

CSndNewValue ==
  /\ sAck = sBit
  /\ sent' \in Data
  /\ sBit' = 1 - sBit
  /\ UNCHANGED << sAck, rBit, rcvd >>

CRcvMsg ==
  /\ rBit # sBit
  /\ rBit' = sBit
  /\ rcvd' = sent
  /\ UNCHANGED << sBit, sAck, sent >>

CRcvAck ==
  /\ rBit # sAck
  /\ sAck' = rBit
  /\ UNCHANGED << sBit, rBit, sent, rcvd >>

CNext == CSndNewValue \/ CRcvMsg \/ CRcvAck

ABCSpec ==
  /\ ABCInit
  /\ [][CNext]_vars
  /\ WF_vars(CRcvMsg)
  /\ WF_vars(CRcvAck)

Spec == ABCSpec

THEOREM ABCSpec => []TypeInv
=============================================================================