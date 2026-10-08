------------------------------- MODULE Channel -------------------------------

CONSTANTS Data

VARIABLE chan

(*--algorithm channel
variables chan = [val \in Data, rdy \in BOOLEAN, ack \in BOOLEAN];

Init == /\ chan.val \in Data
        /\ chan.rdy = chan.ack

TypeInvariant ==
    /\ chan.val \in Data
    /\ chan.rdy \in BOOLEAN
    /\ chan.ack \in BOOLEAN

Send(d) ==
    /\ d \in Data
    /\ chan.rdy = chan.ack
    /\ chan' = [chan EXCEPT !.val = d, !.rdy = ~chan.rdy]

Rcv ==
    /\ chan.rdy # chan.ack
    /\ chan' = [chan EXCEPT !.ack = ~chan.ack]

Next == \/ \E d \in Data : Send(d)
        \/ Rcv

Spec == Init /\ [][Next]_<<chan>>

THEOREM TypeInvariant \in Spec

end algorithm *)
=============================================================================