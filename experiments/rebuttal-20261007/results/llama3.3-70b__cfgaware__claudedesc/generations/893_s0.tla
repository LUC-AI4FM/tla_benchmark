```
MODULE Channel
VARIABLE chan
CONSTANT Data

TypeInvariant == chan \in [val : Data, rdy : {0, 1}, ack : {0, 1}]

Init == chan = [val |-> (CHOOSE d \in Data : TRUE), 
                rdy |-> 0, 
                ack |-> 0] /\ chan.ack = chan.rdy

Send(d) == chan' = [chan EXCEPT !.rdy = IF chan.rdy = 0 THEN 1 ELSE 0,
                                        !.val = d]

Rcv == chan' = [chan EXCEPT !.ack = IF chan.ack = 0 THEN 1 ELSE 0]

Next == \E d \in Data : Send(d) \/ Rcv

Spec == Init /\ [][Next]_chan

THEOREM Spec => []TypeInvariant
```