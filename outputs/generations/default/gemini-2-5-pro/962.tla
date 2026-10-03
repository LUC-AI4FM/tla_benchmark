---- MODULE AlternatingBit ----
EXTENDS Integers, TLC

CONSTANTS Data
ASSUME Data /= {}

VARIABLES sBit, rBit, sAck, sent, received

vars == <<sBit, rBit, sAck, sent, received>>

TypeOK == /\ sBit \in {0, 1}
          /\ rBit \in {0, 1}
          /\ sAck \in {0, 1}
          /\ sent \in Data
          /\ received \in Data

Init == /\ sBit = 0
        /\ sAck = 0
        /\ rBit = 0
        /\ sent \in Data
        /\ received \in Data

\* The sender may send a new value when its acknowledgement bit matches its send bit.
SendMessage(d) == /\ sAck = sBit
                  /\ sBit' = 1 - sBit
                  /\ sent' = d
                  /\ UNCHANGED <<rBit, sAck, received>>

\* The receiver may accept a message when its receive bit differs from the sender bit.
ReceiveMessage == /\ rBit /= sBit
                  /\ received' = sent
                  /\ rBit' = sBit
                  /\ UNCHANGED <<sBit, sAck, sent>>

\* The sender may accept an acknowledgement when the receiver bit differs from the sender acknowledgement bit.
AcceptAck == /\ rBit /= sAck
             /\ sAck' = rBit
             /\ UNCHANGED <<sBit, rBit, sent, received>>

Next == \/ (\E d \in Data : SendMessage(d))
        \/ ReceiveMessage
        \/ AcceptAck

\* Fairness assumptions for message reception and acknowledgement reception.
Fairness == WF_vars(ReceiveMessage) /\ WF_vars(AcceptAck)

Spec == Init /\ [][Next]_vars /\ Fairness

\* The temporal property stating that the sender and acknowledgement bits
\* are infinitely often out of sync.
Liveness == []<> (sBit /= sAck)

====