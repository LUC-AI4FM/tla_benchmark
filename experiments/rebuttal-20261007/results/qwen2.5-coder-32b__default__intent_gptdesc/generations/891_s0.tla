------------------------------- MODULE Handshake -------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS DataValues \* A finite set of possible data values

VARIABLES ready, ack, data

Init == /\ ready = FALSE
        /\ ack = FALSE
        /\ data \in DataValues

Next ==
    \/ /\ ready = ack
       /\ \/ /\ CHOOSE newData \in DataValues : TRUE
              /\ data' = newData
          \/ data' = data
       /\ ready' = ~ready
       /\ ack' = ack
    \/ /\ ready # ack
       /\ data' = data
       /\ ready' = ready
       /\ ack' = ~ack

Spec ==
    /\ Init
    /\ [][Next]_<<ready, ack, data>>
    /\ WF_next(<<ready, ack, data>>, Next)

TypeSafety == /\ ready \in {FALSE, TRUE}
                /\ ack \in {FALSE, TRUE}
                /\ data \in DataValues

DataIntegrity ==
    LET sentValues == {d \in DataValues : <FALSE, TRUE, d> \in [][ready, ack, data]_<<ready, ack, data>>}
        receivedValues == {d \in DataValues : <TRUE, FALSE, d> \in [][ready, ack, data]_<<ready, ack, data>>}
    IN sentValues = receivedValues

NoDeadlock ==
    LET sentEvents == {s \in 1..Len([][ready, ack, data]_<<ready, ack, data>>) : ready' = ~ready /\ ack' = ack}
        receivedEvents == {r \in 1..Len([][ready, ack, data]_<<ready, ack, data>>) : ready' = ready /\ ack' = ~ack}
    IN \/ sentEvents = {}
       \/ Max(sentEvents) < Max(receivedEvents)

Alternation ==
    LET pendingData == {s \in 1..Len([][ready, ack, data]_<<ready, ack, data>>) : ready' = ~ready /\ ack' = ack}
        consumedData == {r \in 1..Len([][ready, ack, data]_<<ready, ack, data>>) : ready' = ready /\ ack' = ~ack}
    IN pendingData = consumedData

Invariant ==
    /\ TypeSafety
    /\ DataIntegrity
    /\ Alternation

Liveness ==
    \/ NoDeadlock
    \/ <>(\E d \in DataValues : <FALSE, TRUE, d> \in [][ready, ack, data]_<<ready, ack, data>>)

=============================================================================