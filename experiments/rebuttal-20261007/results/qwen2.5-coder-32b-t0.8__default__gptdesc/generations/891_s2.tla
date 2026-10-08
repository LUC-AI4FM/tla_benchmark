---- MODULE AsyncSenderReceiver ----
EXTENDS Naturals, FiniteSets

CONSTANTS Data

VARIABLES rdy, ack, val

Init == /\ rdy = 0 
        /\ ack = 0 
        /\ val \in Data

Next ==
    \/ /\ rdy = ack
       /\ \/ \E v \in Data : val' = v
          /\ rdy' = 1 - rdy
          /\ ack' = ack
    \/ /\ rdy # ack
       /\ val' = val
       /\ rdy' = rdy
       /\ ack' = 1 - ack

Spec == Init /\ [][Next]_<<rdy, ack, val>>

TypeInvariant ==
    /\ rdy \in {0, 1}
    /\ ack \in {0, 1}
    /\ val \in Data

THEOREM Spec => []TypeInvariant
====