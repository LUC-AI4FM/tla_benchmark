---- MODULE AsyncReadyAck ----
EXTENDS Naturals

CONSTANT DATA

VARIABLES buf, rdy, ack

Bits == {0, 1}

vars == << buf, rdy, ack >>

Toggle(b) == 1 - b

Init ==
  /\ buf \in DATA
  /\ rdy \in Bits
  /\ ack \in Bits
  /\ ack = rdy

SenderStep ==
  /\ rdy = ack
  /\ buf' \in DATA
  /\ rdy' = Toggle(rdy)
  /\ ack' = ack

ReceiverStep ==
  /\ rdy # ack
  /\ ack' = rdy
  /\ UNCHANGED << buf, rdy >>

Next == SenderStep \/ ReceiverStep

Spec == Init /\ [][Next]_vars

TypeInvariant ==
  /\ buf \in DATA
  /\ rdy \in Bits
  /\ ack \in Bits
====