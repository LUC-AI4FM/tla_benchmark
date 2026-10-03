---------------------------- MODULE Channel --------------------------------
EXTENDS Integers

CONSTANT InitChannel

VARIABLE channel

TypeInvariant == 
  /\ channel.val \in Int
  /\ channel.rdy \in {0, 1}
  /\ channel.ack \in {0, 1}

Send == 
  /\ channel.rdy = channel.ack
  /\ channel' = [channel EXCEPT !.rdy = 1 - channel.rdy, !.val = channel.val + 1]
  /\ UNCHANGED << >>

Receive == 
  /\ channel.rdy # channel.ack
  /\ channel' = [channel EXCEPT !.ack = 1 - channel.ack]
  /\ UNCHANGED << >>

Next == Send \/ Receive

Spec == 
  /\ (channel = InitChannel)
  /\ [][Next]_channel

=============================================================================