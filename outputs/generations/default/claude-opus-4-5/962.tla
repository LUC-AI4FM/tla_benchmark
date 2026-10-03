---------------------------- MODULE AlternatingBit ----------------------------
EXTENDS Naturals, Sequences

CONSTANTS Data

VARIABLES sBit,      \* Sender's current send bit
          sAck,      \* Sender's acknowledgement bit
          rBit,      \* Receiver's bit
          sent,      \* Data value being sent
          received   \* Data value received

vars == <<sBit, sAck, rBit, sent, received>>

TypeInvariant ==
    /\ sBit \in {0, 1}
    /\ sAck \in {0, 1}
    /\ rBit \in {0, 1}
    /\ sent \in Data
    /\ received \in Data

Init ==
    /\ sBit = 0
    /\ sAck = 0
    /\ rBit = 1
    /\ sent \in Data
    /\ received \in Data

\* Sender sends a new value when acknowledgement bit matches send bit
SendNew(d) ==
    /\ sAck = sBit
    /\ sent' = d
    /\ sBit' = 1 - sBit
    /\ UNCHANGED <<sAck, rBit, received>>

\* Receiver accepts message when receive bit differs from sender bit
ReceiveMsg ==
    /\ rBit /= sBit
    /\ received' = sent
    /\ rBit' = sBit
    /\ UNCHANGED <<sBit, sAck, sent>>

\* Sender accepts acknowledgement when receiver bit differs from sender ack bit
ReceiveAck ==
    /\ rBit /= sAck
    /\ sAck' = rBit
    /\ UNCHANGED <<sBit, rBit, sent, received>>

Next ==
    \/ \E d \in Data : SendNew(d)
    \/ ReceiveMsg
    \/ ReceiveAck

Fairness ==
    /\ WF_vars(ReceiveMsg)
    /\ WF_vars(ReceiveAck)

Spec == Init /\ [][Next]_vars /\ Fairness

\* Temporal property: sender and acknowledgement bits are infinitely often out of sync
BitsOutOfSync == sBit /= sAck

Liveness == []<>BitsOutOfSync

THEOREM Spec => []TypeInvariant

THEOREM Spec => Liveness

=============================================================================