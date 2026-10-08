MODULE AltBitProtocol
EXTENDS Naturals

VARIABLES sendBit, recvBit, ackBit, sentData, receivedData

BIT == {0,1}

TypeInvariant ==
    /\ sendBit \in BIT
    /\ recvBit \in BIT
    /\ ackBit \in BIT
    /\ sentData \in Nat
    /\ receivedData \in Nat

Init ==
    /\ sendBit = 0
    /\ recvBit = 0
    /\ ackBit = 0
    /\ sentData = 0
    /\ receivedData = 0

Send ==
    /\ sendBit = ackBit
    /\ \E newData \in Nat :
        /\ sentData' = newData
        /\ sendBit' = 1 - sendBit
        /\ recvBit' = recvBit
        /\ ackBit' = ackBit
        /\ receivedData' = receivedData

ReceiveMessage ==
    /\ recvBit # sendBit
    /\ receivedData' = sentData
    /\ recvBit' = 1 - recvBit
    /\ sendBit' = sendBit
    /\ ackBit' = ackBit
    /\ sentData' = sentData

ReceiveAck ==
    /\ recvBit # ackBit
    /\ ackBit' = recvBit
    /\ sendBit' = sendBit
    /\ recvBit' = recvBit
    /\ sentData' = sentData
    /\ receivedData' = receivedData

Skip == TRUE

Next == Send \/ ReceiveMessage \/ ReceiveAck \/ Skip

vars == <<sendBit, recvBit, ackBit, sentData, receivedData>>

Spec ==
    Init /\ [][Next]_vars
        /\ TypeInvariant
        /\ WF/Inf(ReceiveMessage)
        /\ WF/Inf(ReceiveAck)
        /\ []<>(sendBit # ackBit)