---------------------------- MODULE AsyncInterface ----------------------------
EXTENDS Naturals

CONSTANTS Data

VARIABLES rdy, ack, val

TypeInvariant == /\ rdy \in {0, 1}
                 /\ ack \in {0, 1}
                 /\ val \in Data

Init == /\ rdy = 0
        /\ ack = 0
        /\ val \in Data

Send == /\ rdy = ack
        /\ val' \in Data
        /\ rdy' = 1 - rdy
        /\ UNCHANGED ack

Rcv == /\ rdy # ack
       /\ ack' = 1 - ack
       /\ UNCHANGED <<rdy, val>>

Next == Send \/ Rcv

Spec == Init /\ [][Next]_<<rdy, ack, val>>

THEOREM Spec => []TypeInvariant

===============================================================================