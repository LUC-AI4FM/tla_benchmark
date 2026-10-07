----------------------------- MODULE ABCorrectness -----------------------------
EXTENDS Naturals

CONSTANTS d1, d2

Data == {d1, d2}
Bits == {0, 1}

VARIABLES sBit, sAck, rBit, sent, rcvd

vars == << sBit, sAck, rBit, sent, rcvd >>

Init ==
  /\ sBit \in Bits
  /\ sAck \in Bits
  /\ rBit \in Bits
  /\ sBit = sAck
  /\ rBit = sBit
  /\ sent \in Data
  /\ rcvd \in Data

CSndNewValue ==
  /\ sAck = sBit
  /\ sBit' = 1 - sBit
  /\ sent' \in Data
  /\ UNCHANGED << sAck, rBit, rcvd >>

CRcvMsg ==
  /\ sBit # rBit
  /\ rBit' = sBit
  /\ rcvd' = sent
  /\ UNCHANGED << sBit, sAck, sent >>

CRcvAck ==
  /\ sAck # rBit
  /\ sAck' = rBit
  /\ UNCHANGED << sBit, rBit, sent, rcvd >>

Next ==
  CSndNewValue \/ CRcvMsg \/ CRcvAck

TypeInv ==
  /\ sBit \in Bits
  /\ sAck \in Bits
  /\ rBit \in Bits
  /\ sent \in Data
  /\ rcvd \in Data

ABCSpec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(CRcvMsg)
  /\ WF_vars(CRcvAck)

Spec == ABCSpec
=============================================================================