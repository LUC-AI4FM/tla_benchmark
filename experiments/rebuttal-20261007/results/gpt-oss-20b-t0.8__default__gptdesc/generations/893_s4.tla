MODULE OnePlaceChannel
CONSTANT Vals

VARIABLE channel

TypeInvariant == channel.rdy \in {0,1} /\ channel.ack \in {0,1}

Sender ==
  channel.rdy = channel.ack /\
  \E v \in Vals :
    (channel' = [channel EXCEPT ! .val = v,
                    ! .rdy = 1 - channel.rdy])

Receiver ==
  channel.rdy /= channel.ack /\
  channel' = [channel EXCEPT ! .ack = 1 - channel.ack]

Next == Sender \/ Receiver

Init == channel = [val |-> 0, rdy |-> 0, ack |-> 0]

Spec == Init /\ []Next

THEOREM Preservation == Spec => []TypeInvariant