------------------------------ MODULE SenderReceiver ------------------------------

EXTENDS Naturals, TLC

CONSTANTS Data

VARIABLES rdy, ack, val

Init == /\ rdy = 0
        /\ ack = 0
        /\ val \in Data

Send == \/ /\ rdy = ack
         /\ \/ \E v \in Data : val' = v
         /\ rdy' = (rdy + 1) % 2
         /\ ack' = ack
         /\ val \in Data

Rcv == \/ /\ rdy # ack
        /\ ack' = (ack + 1) % 2
        /\ rdy' = rdy
        /\ val' = val
        /\ val \in Data

Next == Send \/ Rcv

Spec == /\ Init
        /\ [][Next]_<<rdy, ack, val>>
        /\ WF_next(<<rdy, ack, val>>)

TypeInvariant == /\ rdy \in {0, 1}
                   /\ ack \in {0, 1}
                   /\ val \in Data

THEOREM Spec => []TypeInvariant

=============================================================================