------------------------------- MODULE AsyncChannel -------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS Data

VARIABLES chan

ChanType == [val \in Data, rdy \in BOOLEAN, ack \in BOOLEAN]

Init == /\ chan \in ChanType
        /\ chan.ack = chan.rdy

Send(d) == /\ d \in Data
           /\ chan.ack = chan.rdy
           /\ chan' = [chan EXCEPT !.val = d, !.rdy = ~chan.rdy]

Rcv == /\ chan.ack # chan.rdy
       /\ chan' = [chan EXCEPT !.ack = ~chan.ack]

Next == \/ \E d \in Data : Send(d)
        \/ Rcv

Spec == Init /\ [][Next]_<<chan>>

TypeInvariant == \A s \in StateSpace: s.chan \in ChanType

=============================================================================