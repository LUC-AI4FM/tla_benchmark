---- MODULE Handshake ----
EXTENDS TLC

CONSTANT Data

VARIABLES rdy, ack, val

vars == << rdy, ack, val >>

TypeInvariant ==
  /\ rdy \in BOOLEAN
  /\ ack \in BOOLEAN
  /\ val \in Data

Init ==
  /\ rdy \in BOOLEAN
  /\ ack = rdy
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

Next == Send \/ Rcv

Spec == Init /\ [][Next]_vars

THEOREM Spec => []TypeInvariant

====