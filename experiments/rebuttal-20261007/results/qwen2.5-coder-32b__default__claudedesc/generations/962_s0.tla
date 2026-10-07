------------------------------- MODULE ABCorrectness -------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS Data
ASSUME Data = {d1, d2}

VARIABLES sBit, sAck, rBit, sent, rcvd

Init == /\ sBit \in {0, 1}
        /\ sAck = sBit
        /\ rBit = sBit
        /\ sent \in Data
        /\ rcvd \in Data

CSndNewValue == \/ sAck = sBit
                  /\ sent' \in Data \ {sent}
                  /\ sBit' = 1 - sBit
                  /\ UNCHANGED <<sAck, rBit, rcvd>>

CRcvMsg == \/ rBit /= sBit
               /\ rBit' = sBit
               /\ rcvd' = sent
               /\ UNCHANGED <<sBit, sAck, sent>>

CRcvAck == \/ sAck /= rBit
              /\ sAck' = rBit
              /\ UNCHANGED <<sBit, rBit, sent, rcvd>>

Next == CSndNewValue \/ CRcvMsg \/ CRcvAck

Spec == Init /\ [][Next]_<<sBit, sAck, rBit, sent, rcvd>> /\ WF_[CRcvMsg]_<<sBit, sAck, rBit, sent, rcvd>> /\ WF_[CRcvAck]_<<sBit, sAck, rBit, sent, rcvd>>

TypeInv == /\ sBit \in {0, 1}
           /\ sAck \in {0, 1}
           /\ rBit \in {0, 1}
           /\ sent \in Data
           /\ rcvd \in Data

=============================================================================