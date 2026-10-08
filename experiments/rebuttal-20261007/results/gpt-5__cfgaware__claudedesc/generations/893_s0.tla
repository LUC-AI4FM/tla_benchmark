----------------------------- MODULE AsyncOneWayChan -----------------------------

CONSTANT Data
VARIABLE chan

TypeInvariant ==
  chan \in [ val: Data, rdy: BOOLEAN, ack: BOOLEAN ]

Init ==
  /\ TypeInvariant
  /\ chan.ack = chan.rdy

Send(d) ==
  /\ d \in Data
  /\ chan.rdy = chan.ack
  /\ chan' = [chan EXCEPT !.val = d, !.rdy = ~@]

Rcv ==
  /\ chan.rdy # chan.ack
  /\ chan' = [chan EXCEPT !.ack = ~@]

Next ==
  ( \E d \in Data: Send(d) ) \/ Rcv

Spec ==
  Init /\ [][Next]_chan

THEOREM Spec => []TypeInvariant

=============================================================================