----------------------------- MODULE Handshake -----------------------------
EXTENDS Naturals

CONSTANT Data

VARIABLES val, rdy, ack

Vars == << val, rdy, ack >>

Init ==
  /\ val \in Data
  /\ rdy \in {0, 1}
  /\ ack = rdy

Send ==
  /\ rdy = ack
  /\ val' \in Data
  /\ rdy' = 1 - rdy
  /\ ack' = ack

Rcv ==
  /\ rdy /= ack
  /\ val' = val
  /\ rdy' = rdy
  /\ ack' = rdy

Next == Send \/ Rcv

Spec == Init /\ [][Next]_Vars

TypeInvariant ==
  /\ val \in Data
  /\ rdy \in {0, 1}
  /\ ack \in {0, 1}

THEOREM Spec => []TypeInvariant
============================================================================