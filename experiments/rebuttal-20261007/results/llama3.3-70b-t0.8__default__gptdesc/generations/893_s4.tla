```
MODULE Channel
EXTENDS Integers

CONSTANTS ValSet
VARIABLES chan

Init == (chan = [val |-> 0, rdy |-> 0, ack |-> 0])

Send == chan' = [chan EXCEPT !.rdy = 1 - ?.rdy, !.val = IF ?.rdy = ?.ack THEN 1 ELSE ?.val]
Receive == chan' = [chan EXCEPT !.ack = 1 - ?.ack]

Next == (chan.rdy = chan.ack) /\ Send ∨ (chan.rdy ≠ chan.ack) /\ Receive

TypeInvariant == chan ∈ [val : Int, rdy : {0, 1}, ack : {0, 1}]

Spec == Init ∧ □[Next]_chan
THEOREM Spec => []TypeInvariant
```