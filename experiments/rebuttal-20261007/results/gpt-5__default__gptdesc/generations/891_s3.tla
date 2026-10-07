---- MODULE Handshake ----
EXTENDS TLC

CONSTANT Data

VARIABLES rdy, ack, val

vars == << rdy, ack, val >>

Init ==
  /\ rdy = FALSE
  /\ ack = FALSE
  /\ val \in Data

Send ==
  /\ rdy = ack
  /\ rdy' = ~rdy
  /\ ack' = ack
  /\ val' \in Data

Rcv ==
  /\ rdy # ack
  /\ rdy' = rdy
  /\ ack' = ~ack
  /\ val' = val

Next == Send \/ Rcv

TypeInvariant ==
  /\ rdy \in BOOLEAN
  /\ ack \in BOOLEAN
  /\ val \in Data

Spec ==
  /\ Init
  /\ [][Next]_vars

THEOREM Spec => []TypeInvariant

====