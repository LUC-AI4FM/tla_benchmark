---------------------------- MODULE Channel ----------------------------
EXTENDS Naturals

CONSTANT Data

VARIABLE chan

TypeInvariant == chan \in [val : Data, rdy : {0, 1}, ack : {0, 1}]

-----------------------------------------------------------------------------

Init == /\ TypeInvariant
        /\ chan.ack = chan.rdy

Send(d) == /\ chan.rdy = chan.ack
           /\ chan' = [chan EXCEPT !.val = d, !.rdy = 1 - @]

Rcv == /\ chan.rdy # chan.ack
       /\ chan' = [chan EXCEPT !.ack = 1 - @]

Next == (\E d \in Data : Send(d)) \/ Rcv

vars == << chan >>

Spec == /\ Init
        /\ [][Next]_chan
        /\ WF_vars(Rcv)
        /\ WF_vars(\E d \in Data : Send(d))

-----------------------------------------------------------------------------

NoOverwrite == [][\A d \in Data : Send(d) => chan.rdy = chan.ack]_chan

NoSpuriousAck == [][(chan' # chan /\ chan'.ack # chan.ack) => chan.rdy # chan.ack]_chan

HandshakeCompletes == (chan.rdy # chan.ack) ~> (chan.rdy = chan.ack)

EventuallyPending == []<>(chan.rdy # chan.ack)

THEOREM Spec => []TypeInvariant
=============================================================================