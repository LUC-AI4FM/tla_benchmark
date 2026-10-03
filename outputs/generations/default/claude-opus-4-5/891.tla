---------------------------- MODULE AsyncInterface ----------------------------
EXTENDS Naturals

CONSTANTS Data

VARIABLES val, rdy, ack

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

Rcv == /\ rdy # ack
       /\ ack' = 1 - ack
       /\ val' = val
       /\ rdy' = rdy

Next == Send \/ Rcv

Spec == Init /\ [][Next]_<<val, rdy, ack>>

THEOREM Spec => []TypeInvariant

================================================================================