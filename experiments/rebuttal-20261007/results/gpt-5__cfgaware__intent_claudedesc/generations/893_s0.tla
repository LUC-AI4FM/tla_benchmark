------------------------------ MODULE AsyncHandshakeChannel ------------------------------

EXTENDS Naturals

CONSTANT Data

VARIABLE ch

TypeInvariant ==
  ch \in [data: Data, ready: {0,1}, ack: {0,1}]

Idle == ch.ready = ch.ack
Busy == ch.ready # ch.ack

Init ==
  ch \in [data: Data, ready: {0,1}, ack: {0,1}]
  /\ Idle

Send ==
  Idle
  /\ \E d \in Data:
      ch' = [ch EXCEPT !.data = d, !.ready = 1 - @, !.ack = @]

Recv ==
  Busy
  /\ ch' = [ch EXCEPT !.ack = 1 - @]

Next == Send \/ Recv

Spec == Init /\ [][Next]_ch

==============================================================================