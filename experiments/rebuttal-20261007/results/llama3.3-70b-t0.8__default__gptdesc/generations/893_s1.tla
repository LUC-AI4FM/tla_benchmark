```
MODULE Channel
EXTENDS Integers

CONSTANTS NULL
VARIABLES chan

Init == (chan = [val |-> NULL, rdy |-> 0, ack |-> 0])

Send == /\ chan.rdy = chan.ack
        /\ chan' = [chan EXCEPT !.rdy = 1 - chan.rdy, !.val = IF chan.rdy = 0 THEN NULL ELSE chan.val]

Receive == /\ chan.rdy # chan.ack
          /\ chan' = [chan EXCEPT !.ack = 1 - chan.ack]

Next == Send \/ Receive

TypeInv == chan.rdy \in {0, 1} /\ chan.ack \in {0, 1}

Spec == Init /\ [][Next]_chan

THEOREM Spec => []TypeInv
```
Note: `!` is used to denote the new value of a record field in TLA+, not to be confused with logical negation. `EXCEPT` is used to create a new record that is equal to an existing one, except for specified changes. `[Next]_chan` denotes the stuttering closure of `Next` with respect to variable `chan`, which allows `chan` to either change according to `Next` or remain the same.