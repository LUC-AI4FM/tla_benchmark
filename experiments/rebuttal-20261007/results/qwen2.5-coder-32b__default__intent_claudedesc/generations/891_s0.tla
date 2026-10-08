------------------------------- MODULE AsyncInterface -------------------------------

EXTENDS Naturals, FiniteSets

CONSTANTS DataValues

VARIABLES data, ready, ack

Init == /\ data \in DataValues
        /\ ready \in {0, 1}
        /\ ack = ready

Next == \/ /\ ready = ack
           /\ \/ /\ ready' = 1 - ready
              /\ data' \in DataValues
              /\ ack' = ack
          \/ /\ ready # ack
           /\ \/ /\ ack' = ready
              /\ data' = data
              /\ ready' = ready

Spec == Init /\ [][Next]_<<data, ready, ack>>

TypeInvariant == /\ data \in DataValues
                 /\ ready \in {0, 1}
                 /\ ack \in {0, 1}

Inv == TypeInvariant

=============================================================================