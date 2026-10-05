---------------------------- MODULE AsyncChannel ----------------------------

CONSTANT Data

VARIABLE chan

TypeInvariant == chan \in [val : Data, rdy : {0, 1}, ack : {0, 1}]

Init == chan \in [val : Data, rdy : {0, 1}, ack : {0, 1}] /\ chan.rdy = chan.ack

Send == /\ chan.rdy = chan.ack
        /\ \E d \in Data : chan' = [chan EXCEPT !.val = d, !.rdy = 1 - chan.rdy]

Recv == /\ chan.rdy # chan.ack
        /\ chan' = [chan EXCEPT !.ack = 1 - chan.ack]

Next == Send \/ Recv

Spec == Init /\ [][Next]_chan

=============================================================================