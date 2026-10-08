MODULE OnePlaceChannel
EXTENDS Naturals, TLC

CONSTANTS ValSet, InitVal

VARIABLE channel

Init == 
    channel = [val |-> InitVal,
               rdy |-> 0,
               ack |-> 0]

SenderAction ==
    /\ channel.rdy = channel.ack
    /\ \E v \in ValSet :
        channel' = [channel EXCEPT !.rdy = 1 - channel.rdy,
                     !.val = v]

ReceiverAction ==
    /\ channel.rdy # channel.ack
    /\ channel' = [channel EXCEPT !.ack = 1 - channel.ack]

Next == SenderAction \/ ReceiverAction

TypeInv ==
    /\ channel.rdy \in {0,1}
    /\ channel.ack \in {0,1}
    /\ channel.val \in ValSet

Spec == Init /\ [] (Next) /\ [] TypeInv
===============================================================================