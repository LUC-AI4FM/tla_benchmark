```
MODULE Channel
EXTENDS Integers

CONSTANTS None

VARIABLES channel

Init ==
  /\ channel = [val |-> None, rdy |-> 0, ack |-> 0]

Next ==
  \/ (channel.rdy = channel.ack) /\ 
    (channel' = [channel EXCEPT !.rdy = 1 - channel.rdy, !.val = 1])
  \/ (channel.rdy # channel.ack) /\ 
    (channel' = [channel EXCEPT !.ack = 1 - channel.ack])

Spec ==
  Init /\ [][Next]_channel

TypeInvariant ==
  /\ channel.rdy \in {0, 1}
  /\ channel.ack \in {0, 1}

THEOREM Spec => []TypeInvariant
```