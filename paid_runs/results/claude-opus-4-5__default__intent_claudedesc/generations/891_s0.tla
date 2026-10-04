---------------------------- MODULE AsyncInterface ----------------------------
EXTENDS Naturals

CONSTANTS Data

VARIABLES data, ready, ack

vars == <<data, ready, ack>>

TypeInvariant ==
    /\ data \in Data
    /\ ready \in {0, 1}
    /\ ack \in {0, 1}

Init ==
    /\ data \in Data
    /\ ready \in {0, 1}
    /\ ack = ready

Send ==
    /\ ready = ack
    /\ data' \in Data
    /\ ready' = 1 - ready
    /\ UNCHANGED ack

Receive ==
    /\ ready # ack
    /\ ack' = ready
    /\ UNCHANGED <<data, ready>>

Next ==
    \/ Send
    \/ Receive

Spec == Init /\ [][Next]_vars

===============================================================================