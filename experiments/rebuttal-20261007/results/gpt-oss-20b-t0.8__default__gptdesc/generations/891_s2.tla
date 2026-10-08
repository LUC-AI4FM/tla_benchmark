------------------------------ MODULE AsyncHandshake ------------------------------
EXTENDS Naturals, TLC

CONSTANTS Data

VARIABLES rdy, ack, val

TypeInvariant == /\ rdy \in {TRUE, FALSE}
               /\ ack \in {TRUE, FALSE}
               /\ val \in Data

Init ==
  /\ rdy = FALSE
  /\ ack = FALSE
  /\ val \in Data

Sender ==
  /\ rdy = ack
  /\ val' \in Data
  /\ rdy' = ~rdy
  /\ ack' = ack

Receiver ==
  /\ rdy # ack
  /\ ack' = ~ack
  /\ rdy' = rdy
  /\ val' = val

Stutter == /\ rdy' = rdy /\ ack' = ack /\ val' = val

Next == Sender \/ Receiver \/ Stutter

vars == <<rdy, ack, val>>

Spec ==
  Init /\ [] [ Next ]_vars

THEOREM Spec => [] TypeInvariant
=============================================================================