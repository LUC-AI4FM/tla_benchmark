------------------------------ MODULE AsyncSenderReceiver ------------------------------

EXTENDS Naturals

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
  /\ rdy' = ~rdy
  /\ ack' = ack
  /\ val' \in Data

Rcv ==
  /\ rdy # ack
  /\ rdy' = rdy
  /\ ack' = ~ack
  /\ val' = val

Next == Send \/ Rcv

Spec == Init /\ [][Next]_vars

THEOREM Spec => []TypeInvariant

=============================================================================