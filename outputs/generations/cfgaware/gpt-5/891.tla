----------------------------- MODULE AsyncHandshake -----------------------------
CONSTANT Data

VARIABLES rdy, ack, val

vars == << rdy, ack, val >>

TypeInvariant ==
  /\ rdy \in BOOLEAN
  /\ ack \in BOOLEAN
  /\ val \in Data

Init ==
  /\ rdy = FALSE
  /\ ack = FALSE
  /\ val \in Data

Send ==
  /\ rdy = ack
  /\ val' \in Data
  /\ rdy' = ~rdy
  /\ ack' = ack

Rcv ==
  /\ rdy # ack
  /\ ack' = ~ack
  /\ UNCHANGED << rdy, val >>

Next == Send \/ Rcv

Spec == Init /\ [][Next]_vars

THEOREM Spec => []TypeInvariant
=============================================================================