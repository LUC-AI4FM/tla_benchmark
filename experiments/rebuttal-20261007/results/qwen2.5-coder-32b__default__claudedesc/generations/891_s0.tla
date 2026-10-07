------------------------------- MODULE Handshake -------------------------------

EXTENDS Naturals, FiniteSets, TLC

CONSTANTS Data

VARIABLES val, rdy, ack

Init == /\ val \in Data
        /\ rdy \in {0, 1}
        /\ ack = rdy

Send == \/ /\ rdy = ack
          /\ \/ \E v \in Data : val' = v
             /\ rdy' = 1 - rdy
             /\ ack' = ack

Rcv == \/ /\ rdy # ack
         /\ val' = val
         /\ rdy' = rdy
         /\ ack' = rdy

Next == Send \/ Rcv

Spec == Init /\ [][Next]_<<val, rdy, ack>>

TypeInvariant == /\ val \in Data
                 /\ rdy \in {0, 1}
                 /\ ack \in {0, 1}

THEOREM TypeInvariant

=============================================================================