```
MODULE ABCorrectness
EXTENDS Integers, FiniteSets

CONSTANTS Data

VARIABLES sBit, sAck, rBit, sent, rcvd

Init == 
  (sBit \in {0, 1}) /\ 
  (sAck = sBit) /\ 
  (rBit = sBit) /\ 
  (sent \in Data) /\ 
  (rcvd \in Data)

CSndNewValue == 
  (sAck = sBit) /\ 
  (sBit' = 1 - sBit) /\ 
  (sent' \in Data) /\ 
  (sAck' = sBit') /\ 
  (rBit' = rBit) /\ 
  (rcvd' = rcvd)

CRcvMsg == 
  (rBit # sBit) /\ 
  (rBit' = sBit) /\ 
  (rcvd' = sent) /\ 
  (sAck' = sAck) /\ 
  (sBit' = sBit) /\ 
  (sent' = sent)

CRcvAck == 
  (sAck < rBit) /\ 
  (sAck' = rBit) /\ 
  (rBit' = rBit) /\ 
  (sBit' = sBit) /\ 
  (sent' = sent) /\ 
  (rcvd' = rcvd)

Next == 
  (CSndNewValue) \/ 
  (CRcvMsg) \/ 
  (CRcvAck) \/ 
  (UNCHANGED <<sBit, sAck, rBit, sent, rcvd>>)

TypeInv == 
  (sBit \in {0, 1}) /\ 
  (sAck \in {0, 1}) /\ 
  (rBit \in {0, 1}) /\ 
  (sent \in Data) /\ 
  (rcvd \in Data)

Spec == 
  Init /\ [][Next]_<<sBit, sAck, rBit, sent, rcvd>> /\ 
  WF_vars(CRcvMsg, <<sBit, sAck, rBit, sent, rcvd>>) /\ 
  WF_vars(CRcvAck, <<sBit, sAck, rBit, sent, rcvd>>)

THEOREM Spec => []TypeInv
```