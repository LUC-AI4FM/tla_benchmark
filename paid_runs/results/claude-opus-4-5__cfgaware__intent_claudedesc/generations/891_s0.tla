---------------------------- MODULE AsyncInterface ----------------------------
EXTENDS Naturals

CONSTANT Data

VARIABLES val, rdy, ack

vars == <<val, rdy, ack>>

TypeInvariant == /\ val \in Data
                 /\ rdy \in {0, 1}
                 /\ ack \in {0, 1}

Init == /\ val \in Data
        /\ rdy \in {0, 1}
        /\ ack = rdy

Send == /\ rdy = ack
        /\ val' \in Data
        /\ rdy' = 1 - rdy
        /\ ack' = ack

Receive == /\ rdy # ack
           /\ ack' = rdy
           /\ val' = val
           /\ rdy' = rdy

Next == Send \/ Receive

Spec == Init /\ [][Next]_vars

=============================================================================