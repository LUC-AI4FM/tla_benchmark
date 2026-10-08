------------------------------- MODULE AsyncHandshake -------------------------------

CONSTANTS DataValues \* A finite set of possible data values

VARIABLES senderData, receiverData, ready, acknowledge

\* Initial predicate
Init == /\ senderData \in DataValues
        /\ receiverData = senderData
        /\ ready = FALSE
        /\ acknowledge = FALSE

\* Next-state relation for the sender
NextSender ==
    \/ /\ ready = acknowledge
       /\ \/ senderData' = CHOOSE d \in DataValues : TRUE
          \/ senderData' = senderData
       /\ ready' = ~ready
       /\ acknowledge' = acknowledge
    \/ /\ senderData' = senderData
       /\ ready' = ready
       /\ acknowledge' = acknowledge

\* Next-state relation for the receiver
NextReceiver ==
    \/ /\ ready # acknowledge
       /\ receiverData' = senderData
       /\ ready' = ready
       /\ acknowledge' = ~acknowledge
    \/ /\ receiverData' = receiverData
       /\ ready' = ready
       /\ acknowledge' = acknowledge

\* Full next-state relation
Next == \/ \E s \in {NextSender} : s
        \/ \E r \in {NextReceiver} : r

\* Type invariants
TypeInvariant ==
    /\ senderData \in DataValues
    /\ receiverData \in DataValues
    /\ ready \in BOOLEAN
    /\ acknowledge \in BOOLEAN

\* Data integrity invariant
DataIntegrity ==
    \/ ready = acknowledge
    \/ receiverData' = senderData

\* Handshake alternation invariant
HandshakeAlternation ==
    \/ ready = acknowledge
    \/ ready # acknowledge

\* Specification
Spec == Init /\ [][Next]_<<senderData, receiverData, ready, acknowledge>>

\* Liveness property: eventual acknowledgment of each send
Liveness ==
    \A d \in DataValues : <>[] (ready = ~acknowledge) => <><> (receiverData' = d)

=============================================================================