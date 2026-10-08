------------------------------ MODULE ABCorrectness ------------------------------

EXTENDS Naturals

CONSTANT Data

VARIABLES sBit, sAck, rBit, sent, rcvd

Vars == << sBit, sAck, rBit, sent, rcvd >>

Init ==
  /\ sBit \in {0, 1}
  /\ rBit = sBit
  /\ sAck = sBit
  /\ sent \in Data
  /\ rcvd \in Data

CSndNewValue ==
  /\ sAck = sBit
  /\ sBit' = 1 - sBit
  /\ sent' \in Data
  /\ UNCHANGED << sAck, rBit, rcvd >>

CRcvMsg ==
  /\ rBit # sBit
  /\ rBit' = sBit
  /\ rcvd' = sent
  /\ UNCHANGED << sBit, sAck, sent >>

CRcvAck ==
  /\ sAck # rBit
  /\ sAck' = rBit
  /\ UNCHANGED << sBit, rBit, sent, rcvd >>

Next == CSndNewValue \/ CRcvMsg \/ CRcvAck

TypeInv ==
  /\ sBit \in {0, 1}
  /\ sAck \in {0, 1}
  /\ rBit \in {0, 1}
  /\ sent \in Data
  /\ rcvd \in Data

ABCSpec ==
  Init /\ [][Next]_Vars /\ WF_Vars(CRcvMsg) /\ WF_Vars(CRcvAck)

===============================================================================