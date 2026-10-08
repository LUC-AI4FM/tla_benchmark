------------------------------- MODULE AsyncChannel -------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS DataValues \* The finite set of data items

VARIABLES value, ready, ack

Init == /\ value \in DataValues
        /\ ready = 0
        /\ ack = 0

Send ==
    /\ ready = ack
    /\ \/ \E v \in DataValues : value' = v
       /\ ready' = 1 - ready
       /\ ack' = ack

Receive ==
    /\ ready # ack
    /\ value' = value
    /\ ready' = ready
    /\ ack' = ready

Next == Send \/ Receive

Spec == Init /\ [][Next]_<<value, ready, ack>>

\* Invariants
TypeInvariant == /\ value \in DataValues
                 /\ ready \in {0, 1}
                 /\ ack \in {0, 1}

ProtocolInvariant == \/ (ready = ack) => (UNCHANGED <<value, ready, ack>>)
                     \/ (ready # ack)

\* Liveness properties
ReliableHandshake ==
    <>[](ready = ack => <>(ready' # ack))

\* Fairness conditions
WF_Send_Receive == WFNext(<<Send, Receive>>, <<value, ready, ack>>)

THEOREM Spec => []TypeInvariant
THEOREM Spec => []ProtocolInvariant
THEOREM Spec /\ WF_Send_Receive => ReliableHandshake

=============================================================================