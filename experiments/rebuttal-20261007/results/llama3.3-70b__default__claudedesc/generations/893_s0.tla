```
MODULE Channel
EXTENDS Integers, TLC
CONSTANTS Data
VARIABLES chan

TypeInvariant == chan \in [val : Data, rdy : {0, 1}, ack : {0, 1}]

Init ==
  /\ TypeInvariant
  /\ chan.ack = chan.rdy

Send(d) ==
  /\ chan.rdy = chan.ack
  /\ chan' = [chan EXCEPT !.val = d, !.rdy = 1 - chan.rdy]
  /\ UNCHANGED << >>

Rcv ==
  /\ chan.rdy # chan.ack
  /\ chan' = [chan EXCEPT !.ack = 1 - chan.ack]
  /\ UNCHANGED << >>

Next ==
  \E d \in Data : Send(d)
  \/ Rcv

Spec == Init /\ [][Next]_chan

THEOREM Spec => []TypeInvariant
```