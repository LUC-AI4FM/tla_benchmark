```
MODULE Channel
EXTENDS Integers

CONSTANTS None

VARIABLES channel

Init == (channel = [val |-> 0, rdy |-> 0, ack |-> 0])

Send == IF channel.rdy = channel.ack
        THEN channel' = [channel EXCEPT !.rdy = 1 - channel.rdy, !.val = 1]
        ELSE FALSE

Receive == IF channel.rdy # channel.ack
           THEN channel' = [channel EXCEPT !.ack = 1 - channel.ack]
           ELSE FALSE

Next == Send \/ Receive

TypeInv == channel.rdy \in {0, 1} /\ channel.ack \in {0, 1}

Spec == Init /\ [][Next]_channel

THEOREM Spec => []TypeInv
```