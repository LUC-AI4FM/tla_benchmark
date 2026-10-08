```
MODULE Channel
EXTENDS Integers

CONSTANTS None

VARIABLES chan

Init == (chan = [val |-> 0, rdy |-> 0, ack |-> 0])

Send == chan.rdy = chan.ack /\
          chan' = [chan EXCEPT !.rdy = 1 - chan.rdy, !.val = IF chan.rdy = 1 THEN 1 ELSE 0]

Receive == chan.rdy # chan.ack /\
             chan' = [chan EXCEPT !.ack = 1 - chan.ack]

Next == Send \/ Receive

TypeInv == chan.rdy \in {0, 1} /\ 
           chan.ack \in {0, 1} /\ 
           chan.val \in {0, 1}

Spec == Init /\ [][Next]_chan
```