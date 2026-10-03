---- MODULE OnePlaceChannel ----
EXTENDS Integers

CONSTANT Data

VARIABLE channel

vars == <<channel>>

TypeInvariant ==
    /\ channel.val \in Data
    /\ channel.rdy \in {0, 1}
    /\ channel.ack \in {0, 1}

Init ==
    /\ channel.rdy = 0
    /\ channel.ack = 0
    /\ \E d \in Data : channel = [val |-> d, rdy |-> 0, ack |-> 0]

Send(d) ==
    /\ channel.rdy = channel.ack
    /\ channel' = [channel EXCEPT !.val = d, !.rdy = 1 - @]

Receive ==
    /\ channel.rdy /= channel.ack
    /\ channel' = [channel EXCEPT !.ack = 1 - @]

Next ==
    \/ (\E d \in Data : Send(d))
    \/ Receive

Spec == Init /\ [][Next]_vars

=============================================================================