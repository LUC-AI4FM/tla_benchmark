---------------------------- MODULE Channel ----------------------------

CONSTANT Data

VARIABLES chan

TypeInvariant == chan \in [ val: Data, rdy: BOOLEAN, ack: BOOLEAN ]

Idle    == chan.rdy = chan.ack
Pending == chan.rdy # chan.ack

Init ==
  /\ TypeInvariant
  /\ Idle

Send(d) ==
  /\ Idle
  /\ d \in Data
  /\ chan' = [chan EXCEPT !.val = d, !.rdy = ~@]

Rcv ==
  /\ Pending
  /\ chan' = [chan EXCEPT !.ack = ~@]

Next ==
  ( \E d \in Data: Send(d) )
  \/ Rcv

Spec ==
  Init /\ [][Next]_chan

THEOREM Spec => []TypeInvariant

=============================================================================