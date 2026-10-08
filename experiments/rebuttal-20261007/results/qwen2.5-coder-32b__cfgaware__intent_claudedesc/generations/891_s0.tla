------------------------------- MODULE AsyncBuffer -------------------------------

CONSTANTS DataValues \* A finite set of possible data values

VARIABLES data, ready, ack

\* Initial predicate: acknowledge signal equals the ready signal
Init == /\ data \in DataValues
        /\ ready \in {0, 1}
        /\ ack = ready

\* Next-state relation for the sender
SenderNext ==
    \/ /\ ready = ack
       /\ \/ /\ data' \in DataValues
          /\ ready' = 1 - ready
          /\ ack' = ack
       \/ /\ data' = data
          /\ ready' = ready
          /\ ack' = ack

\* Next-state relation for the receiver
ReceiverNext ==
    \/ /\ ready # ack
       /\ data' = data
       /\ ready' = ready
       /\ ack' = 1 - ack
    \/ /\ ready = ack
       /\ data' = data
       /\ ready' = ready
       /\ ack' = ack

\* Next-state relation allowing stuttering steps
Next == SenderNext \/ ReceiverNext

\* Type invariant: data must be in DataValues, and both ready and ack must be single bits
TypeInvariant == /\ data \in DataValues
                 /\ ready \in {0, 1}
                 /\ ack \in {0, 1}

\* Specification: initial state and next-state relation
Spec == Init /\ [][Next]_<<data, ready, ack>>

=============================================================================