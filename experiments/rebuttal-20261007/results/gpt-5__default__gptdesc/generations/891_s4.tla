------------------------------ MODULE AsyncSenderReceiver ------------------------------

CONSTANT Data

VARIABLES rdy, ack, val

vars == << rdy, ack, val >>

TypeInvariant ==
  /\ rdy \in BOOLEAN
  /\ ack \in BOOLEAN
  /\ val \in Data

Init ==
  /\ rdy \in BOOLEAN
  /\ ack \in BOOLEAN
  /\ rdy = ack
  /\ val \in Data

Send ==
  /\ rdy = ack
  /\ val' \in Data
  /\ rdy' = ~rdy
  /\ ack' = ack

Rcv ==
  /\ rdy # ack
  /\ rdy' = rdy
  /\ val' = val
  /\ ack' = ~ack

Next == Send \/ Rcv

Spec == Init /\ [][Next]_vars

THEOREM Spec => []TypeInvariant

=============================================================================