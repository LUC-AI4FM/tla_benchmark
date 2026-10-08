------------------------------ MODULE Handshake ------------------------------
EXTENDS Integers

CONSTANT Data

VARIABLES val, rdy, ack

Init ==
    /\ val \in Data
    /\ rdy \in {0,1}
    /\ ack = rdy

Send ==
    /\ rdy = ack
    /\ val' \in Data
    /\ rdy' = 1 - rdy
    /\ ack' = ack

Rcv ==
    /\ rdy \ne ack
    /\ ack' = rdy
    /\ val' = val
    /\ rdy' = rdy

Next == Send \/ Rcv

Spec == Init /\ [] Next

TypeInvariant ==
    /\ val \in Data
    /\ rdy \in {0,1}
    /\ ack \in {0,1}

THEOREM TypeInvariant IS INVARIANT OF Spec
=============================================================================