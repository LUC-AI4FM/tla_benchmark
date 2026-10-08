------------------------------ MODULE HandshakeBuffer ------------------------------

EXTENDS Integers

CONSTANT DATA

VARIABLES data, rdy, ack

Bits == {0, 1}

vars == << data, rdy, ack >>

TypeInvariant ==
  /\ data \in DATA
  /\ rdy \in Bits
  /\ ack \in Bits

Init ==
  /\ TypeInvariant
  /\ ack = rdy

Sender ==
  /\ rdy = ack
  /\ data' \in DATA
  /\ rdy' = 1 - rdy
  /\ ack' = ack

Receiver ==
  /\ rdy # ack
  /\ data' = data
  /\ rdy' = rdy
  /\ ack' = rdy

Next == Sender \/ Receiver

Spec == Init /\ [][Next]_vars

THEOREM Spec => []TypeInvariant

=============================================================================