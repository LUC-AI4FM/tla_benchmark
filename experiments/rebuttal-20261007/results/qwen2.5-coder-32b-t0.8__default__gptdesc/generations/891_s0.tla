------------------------------ MODULE SenderReceiver ------------------------------

EXTENDS Naturals, FiniteSets

CONSTANTS Data

VARIABLES rdy, ack, val

Init == /\ rdy = FALSE
        /\ ack = FALSE
        /\ val \in Data

Next == \/ /\ rdy = ack
            /\ \/ \E v \in Data : val' = v
               /\ rdy' = NOT rdy
               /\ ack' = ack
         \/ /\ rdy # ack
            /\ rdy' = rdy
            /\ ack' = NOT ack
            /\ val' = val

Spec == Init /\ [][Next]_<<rdy, ack, val>>

TypeInvariant == /\ rdy \in {TRUE, FALSE}
                   /\ ack \in {TRUE, FALSE}
                   /\ val \in Data

=============================================================================