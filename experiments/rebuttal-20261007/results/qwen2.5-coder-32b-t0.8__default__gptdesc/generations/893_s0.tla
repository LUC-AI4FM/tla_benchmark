------------------------------ MODULE HandshakeChannel ------------------------------

EXTENDS Integers

CONSTANTS Domain

VARIABLES val, rdy, ack

Init == /\ val \in Domain
        /\ rdy = 0
        /\ ack = 0

Send == \/ /\ rdy = ack
          /\ \/ \E v \in Domain : val' = v
             /\ rdy' = 1 - rdy
             /\ ack' = ack

Receive == \/ /\ rdy # ack
           /\ val' = val
           /\ rdy' = rdy
           /\ ack' = 1 - ack

Next == Send \/ Receive

TypeInvariant == /\ rdy \in {0, 1}
                 /\ ack \in {0, 1}

Spec ==
    /\ Init
    /\ [][Next]_<<val, rdy, ack>>
    /\ WF_next(<<val, rdy, ack>>)

=============================================================================