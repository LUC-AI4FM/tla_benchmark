---------------------------- MODULE Handshake ----------------------------
CONSTANTS DataSet

VARIABLES ready, ack, data, senderData, delivered

vars == <<ready, ack, data, senderData, delivered>>

TypeInvariant ==
    /\ ready \in {0, 1}
    /\ ack \in {0, 1}
    /\ data \in DataSet
    /\ senderData \in DataSet
    /\ delivered \in DataSet \cup {<<>>}

Init ==
    /\ ready = 0
    /\ ack = 0
    /\ data \in DataSet
    /\ senderData = data
    /\ delivered = <<>>

SenderSend ==
    /\ ready = ack
    /\ \E d \in DataSet:
        /\ data' = d
        /\ senderData' = d
        /\ ready' = 1 - ready
    /\ UNCHANGED <<ack, delivered>>

ReceiverAck ==
    /\ ready # ack
    /\ delivered' = data
    /\ ack' = 1 - ack
    /\ UNCHANGED <<ready, data, senderData>>

Next ==
    \/ SenderSend
    \/ ReceiverAck

Fairness ==
    /\ WF_vars(SenderSend)
    /\ WF_vars(ReceiverAck)

Spec == Init /\ [][Next]_vars /\ Fairness

HandshakeInvariant ==
    IF ready # ack
    THEN data = senderData
    ELSE TRUE

DataIntegrity ==
    (delivered # <<>>) => (delivered \in DataSet)

DeliveredMatchesSent ==
    (ready = ack /\ delivered # <<>>) => (delivered = senderData)

NoDeadlock ==
    (ready # ack) => ENABLED ReceiverAck

EventualAck ==
    [](ready # ack => <>(ready = ack))

Liveness ==
    EventualAck

==========================================================================