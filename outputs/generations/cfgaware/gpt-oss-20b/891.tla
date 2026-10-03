------------------------------ MODULE Handshake ------------------------------
CONSTANTS Data

VARIABLES rdy, ack, val

Init ==
    /\ rdy = TRUE
    /\ ack = TRUE
    /\ val \in Data

Send ==
    /\ rdy = ack
    /\ rdy' = ~rdy
    /\ ack' = ack
    /\ val' \in Data

Rcv ==
    /\ rdy # ack
    /\ ack' = ~ack
    /\ rdy' = rdy
    /\ val' = val

Stutter ==
    /\ rdy' = rdy
    /\ ack' = ack
    /\ val' = val

Next == Send \/ Rcv \/ Stutter

Spec == Init /\ []Next

TypeInvariant ==
    /\ rdy \in {TRUE, FALSE}
    /\ ack \in {TRUE, FALSE}
    /\ val \in Data

THEOREM Spec => []TypeInvariant
------------------------------ END MODULE ------------------------------