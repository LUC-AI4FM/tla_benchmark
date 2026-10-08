```
MODULE Channel
EXTENDS Integers

CONSTANTS None

VARIABLES channel

Init == (channel = [val |-> 0, rdy |-> 0, ack |-> 0])

Send == /\ channel.rdy = channel.ack
        /\ channel' = [channel EXCEPT !.rdy = 1 - channel.rdy, !.val = channel.val + 1]

Receive == /\ channel.rdy # channel.ack
          /\ channel' = [channel EXCEPT !.ack = 1 - channel.ack]

Next == \/ Send
        \/ Receive

TypeInv == /\ channel.rdy \in {0, 1}
          /\ channel.ack \in {0, 1}
          /\ channel.val \in Int

Spec == Init /\ [][Next]_channel
```