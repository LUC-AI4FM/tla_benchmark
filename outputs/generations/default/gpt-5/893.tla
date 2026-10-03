---- MODULE HandshakeChannel ----
EXTENDS Naturals

CONSTANT Values

VARIABLES ch

TypeOK ==
  ch \in [ val: Values, rdy: {0, 1}, ack: {0, 1} ]

Init ==
  ch \in [ val: Values, rdy: {0}, ack: {0} ]

Send(v) ==
  /\ ch.rdy = ch.ack
  /\ v \in Values
  /\ ch' = [ch EXCEPT !.val = v, !.rdy = 1 - @]

Receive ==
  /\ ch.rdy # ch.ack
  /\ ch' = [ch EXCEPT !.ack = 1 - @]

Next ==
  (\E v \in Values: Send(v)) \/ Receive

Spec ==
  Init /\ [][Next]_ch

Invariant == TypeOK

THEOREM Spec => []Invariant

====