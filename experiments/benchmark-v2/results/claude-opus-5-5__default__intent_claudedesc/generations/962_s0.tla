---------------------------- MODULE ABCorrectness ----------------------------
EXTENDS Naturals

CONSTANTS Data

VARIABLES sBit, sAck, rBit, sent, rcvd

vars == <<sBit, sAck, rBit, sent, rcvd>>

TypeOK ==
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

\* Sender chooses a new value and toggles its bit when acknowledged
CSndP ==
    /\ sAck = sBit
    /\ sent' \in Data
    /\ sBit' = 1 - sBit
    /\ UNCHANGED <<sAck, rBit, rcvd>>

\* Receiver copies the sent value and updates its bit
CRcvP ==
    /\ rBit # sBit
    /\ rBit' = sBit
    /\ rcvd' = sent
    /\ UNCHANGED <<sBit, sAck, sent>>

\* Sender updates its acknowledgment bit to match the receiver's bit
CRcvA ==
    /\ sAck # rBit
    /\ sAck' = rBit
    /\ UNCHANGED <<sBit, rBit, sent, rcvd>>

Next == CSndP \/ CRcvP \/ CRcvA

Spec == Init /\ [][Next]_vars /\ WF_vars(CRcvP) /\ WF_vars(CRcvA)

THEOREM Spec => []TypeOK
=============================================================================