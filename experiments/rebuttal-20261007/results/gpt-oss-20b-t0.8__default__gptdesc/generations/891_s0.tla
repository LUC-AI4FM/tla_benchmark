MODULE Handshake
CONSTANTS Data

VARIABLES rdy, ack, val

BOOLEAN == {TRUE, FALSE}

vars == <<rdy, ack, val>>

Init ==
    /\ rdy = TRUE
    /\ ack = TRUE
    /\ val \in Data

Send ==
    /\ rdy = ack
    /\ val' \in Data
    /\ rdy' = ~rdy
    /\ ack' = ack

Rcv ==
    /\ rdy # ack
    /\ rdy' = rdy
    /\ ack' = ~ack
    /\ val' = val

Stutter ==
    /\ rdy' = rdy
    /\ ack' = ack
    /\ val' = val

Next == Send \/ Rcv \/ Stutter

TypeInv ==
    /\ rdy \in BOOLEAN
    /\ ack \in BOOLEAN
    /\ val \in Data

Spec == Init /\ [][Next]_vars

THEOREM Spec_Imply_TypeInv == Spec => []TypeInv