------------------------------- MODULE AsyncChannel -------------------------------

CONSTANTS DataValues \* The finite set of data items that can be sent

VARIABLES value, ready, ack

\* Initialization predicate
Init == /\ value \in DataValues
        /\ ready = 0
        /\ ack = 0

\* Type invariants
TypeInvariant == /\ value \in DataValues
                 /\ ready \in {0, 1}
                 /\ ack \in {0, 1}

\* Next-state relation for sending a message
Send ==
    \/ /\ ready = ack
       /\ \/ \E v \in DataValues : value' = v
          /\ ready' = (ready + 1) % 2
          /\ ack' = ack

\* Next-state relation for acknowledging a message
Receive ==
    \/ /\ ready # ack
       /\ value' = value
       /\ ready' = ready
       /\ ack' = ready

\* Full next-state relation
Next == Send \/ Receive

\* Specification of the system
Spec == Init /\ [][Next]_<<value, ready, ack>> /\ WF_[Next]_<<value, ready, ack>>

\* Invariant: ready equals ack only at initialization or after a receiver step acknowledges
ReadyAckInvariant ==
    \/ /\ value = DataValues[1]
       /\ ready = 0
       /\ ack = 0
    \/ ready = ack

THEOREM Spec => []TypeInvariant
PROOF BY INVARIANT TypeInvariant

THEOREM Spec => [](ready = ack => ReadyAckInvariant)
PROOF BY INVARIANT ReadyAckInvariant

=============================================================================