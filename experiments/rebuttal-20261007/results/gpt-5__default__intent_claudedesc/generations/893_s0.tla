----------------------------- MODULE AsyncOneWayChannel -----------------------------

EXTENDS Naturals, FiniteSets

CONSTANT Data

ASSUME Cardinality(Data) = 3

VARIABLE chan

Bits == {0, 1}

ChannelState == [data: Data, rdy: Bits, ack: Bits]

TypeInv == chan \in ChannelState

Idle == chan.rdy = chan.ack
Busy == chan.rdy # chan.ack

Toggle(b) == 1 - b

Init ==
  TypeInv /\ Idle

Sender ==
  Idle /\
  ∃ d \in Data:
    chan' = [chan EXCEPT
               !.data = d,
               !.rdy  = Toggle(@.rdy),
               !.ack  = @.ack]

Receiver ==
  Busy /\
  chan' = [chan EXCEPT
             !.ack  = Toggle(@.ack),
             !.rdy  = @.rdy,
             !.data = @.data]

Next == Sender \/ Receiver

Spec == Init /\ [][Next]_chan

=============================================================================