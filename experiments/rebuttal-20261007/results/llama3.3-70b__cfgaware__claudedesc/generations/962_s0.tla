---------------------------- MODULE ABCorrectness ----------------------------
EXTENDS Integers, FiniteSets

CONSTANT Data

VARIABLE sBit, sAck, rBit, sent, rcvd

TypeInv == 
  /\ sBit \in {0, 1}
  /\ sAck \in {0, 1}
  /\ rBit \in {0, 1}
  /\ sent \in Data
  /\ rcvd \in Data

Init == 
  /\ sBit \in {0, 1}
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
  /\ sAck < rBit
  /\ sAck' = rBit
  /\ UNCHANGED <<sBit, rBit, sent, rcvd>>

Next == 
  \/ CSndNewValue
  \/ CRcvMsg
  \/ CRcvAck
  \/ UNCHANGED <<sBit, sAck, rBit, sent, rcvd>>

ABCSpec == 
  Init /\ [][Next]_<<sBit, sAck, rBit, sent, rcvd>> 
  /\ WF_vars(CRcvMsg, <<sBit, sAck, rBit, sent, rcvd>>) 
  /\ WF_vars(CRcvAck, <<sBit, sAck, rBit, sent, rcvd>>)
=============================================================================