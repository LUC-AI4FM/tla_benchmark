---------------------------- MODULE AsyncChannel ----------------------------
EXTENDS Integers

CONSTANTS Data

VARIABLES chan

TypeInvariant ==
    /\ chan.data \in Data
    /\ chan.rdy \in {0, 1}
    /\ chan.ack \in {0, 1}

Init ==
    /\ chan = [data |-> CHOOSE d \in Data : TRUE, rdy |-> 0, ack |-> 0]

Send(d) ==
    /\ chan.rdy = chan.ack
    /\ chan' = [chan EXCEPT !.data = d, !.rdy = 1 - chan.rdy]

Receive ==
    /\ chan.rdy # chan.ack
    /\ chan' = [chan EXCEPT !.ack = 1 - chan.ack]

Next ==
    \/ \E d \in Data : Send(d)
    \/ Receive

Spec == Init /\ [][Next]_chan

THEOREM Spec => []TypeInvariant

=============================================================================