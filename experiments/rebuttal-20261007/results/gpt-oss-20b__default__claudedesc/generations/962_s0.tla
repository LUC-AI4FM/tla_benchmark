------------------------------ MODULE ABCorrectness ------------------------------
EXTENDS TLC

CONSTANTS Data

VARIABLES sBit, sAck, rBit, sent, rcvd

vars == <<sBit, sAck, rBit, sent, rcvd>>

Init ==
  /\ sBit \in {0,1}
  /\ sAck = sBit
  /\ rBit = sBit
  /\ sent \in Data
  /\ rcvd \in Data

CSndNewValue ==
  /\ sAck = sBit
  /\ sent' \in Data
  /\ sBit' = 1 - sBit
  /\ UNCHANGED <<sAck, rBit, rcvd>>

CRcvMsg ==
  /\ rBit # sBit
  /\ rBit' = sBit
  /\ rcvd' = sent
  /\ UNCHANGED <<sBit, sAck, sent>>

CRcvAck ==
  /\ sAck # rBit
  /\ sAck' = rBit
  /\ UNCHANGED <<sBit, rBit, sent, rcvd>>

Stutter ==
  UNCHANGED vars

Next == \/ CSndNewValue \/ CRcvMsg \/ CRcvAck \/ Stutter

TypeInv ==
  /\ sBit \in {0,1}
  /\ sAck \in {0,1}
  /\ rBit \in {0,1}
  /\ sent \in Data
  /\ rcvd \in Data

Spec == Init /\ [][Next]_vars /\ WF_vars(CRcvMsg) /\ WF_vars(CRcvAck)

=============================================================================