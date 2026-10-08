------------------------------ MODULE HANDSHAKE ------------------------------

EXTENDS Integers

CONSTANT Data

VARIABLES val, rdy, ack

vars == <<val, rdy, ack>>

Init ==
  /\ val \in Data
  /\ rdy \in {0, 1}
  /\ ack = rdy

Send ==
  /\ rdy = ack
  /\ val' \in Data
  /\ rdy' = 1 - rdy
  /\ UNCHANGED ack

Rcv ==
  /\ rdy # ack
  /\ ack' = rdy
  /\ UNCHANGED <<val, rdy>>

Next == Send \/ Rcv

Spec == Init /\ [][Next]_vars

TypeInvariant ==
  /\ val \in Data
  /\ rdy \in {0, 1}
  /\ ack \in {0, 1}

THEOREM Spec => []TypeInvariant

=============================================================================