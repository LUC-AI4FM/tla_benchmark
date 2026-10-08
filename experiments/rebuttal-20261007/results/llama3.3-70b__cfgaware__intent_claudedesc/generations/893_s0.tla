---------------------------- MODULE ChannelSpec ----------------------------
EXTENDS Integers, TLC

CONSTANT DataValues
VARIABLES channel

TypeInvariant == 
  /\ channel.data \in DataValues
  /\ channel.ready \in {0, 1}
  /\ channel.ack \in {0, 1}

Init ==
  /\ channel = [data |-> (CHOOSE d \in DataValues : TRUE), ready |-> 0, ack |-> 0]

Send ==
  /\ channel.ready = channel.ack
  /\ channel' = [channel EXCEPT !.ready = 1 - channel.ready, !.data = CHOOSE d \in DataValues : TRUE]
  /\ UNCHANGED << >>

Receive ==
  /\ channel.ready # channel.ack
  /\ channel' = [channel EXCEPT !.ack = 1 - channel.ack]
  /\ UNCHANGED << >>

Next == Send \/ Receive

Spec == Init /\ [][Next]_channel

=============================================================================