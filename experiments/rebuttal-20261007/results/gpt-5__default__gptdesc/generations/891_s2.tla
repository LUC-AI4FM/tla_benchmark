------------------------------ MODULE AsyncHandshake ------------------------------

EXTENDS Naturals, TLC

CONSTANT Data

VARIABLES rdy, ack, val

vars == << rdy, ack, val >>

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
  /\ rdy' = rdy
  /\ val' = val

Next == Send \/ Rcv

TypeInvariant ==
  /\ rdy \in BOOLEAN
  /\ ack \in BOOLEAN
  /\ val \in Data

Spec == Init /\ [][Next]_vars

THEOREM SpecImpliesTypeInvariant == Spec => []TypeInvariant

============================================================================