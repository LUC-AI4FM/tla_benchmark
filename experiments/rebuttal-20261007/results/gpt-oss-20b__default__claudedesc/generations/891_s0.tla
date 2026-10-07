------------------------------ MODULE Handshake ------------------------------
EXTENDS TLC

CONSTANTS Data

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
  /\ rdy # ack
  /\ ack' = rdy
  /\ val' = val
  /\ rdy' = rdy

Next == Send \/ Rcv

Stutter ==
  \E val', rdy', ack' :
    /\ val' = val
    /\ rdy' = rdy
    /\ ack' = ack

Spec == Init /\ [] (Next \/ Stutter)

TypeInvariant ==
  /\ val \in Data
  /\ rdy \in {0,1}
  /\ ack \in {0,1}

THEOREM TypeInvariant == INV_OF Spec
=============================================================================