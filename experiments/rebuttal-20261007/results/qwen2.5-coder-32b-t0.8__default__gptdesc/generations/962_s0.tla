```tla
MODULE AlternatingBitProtocol

EXTENDS Naturals, TLC, FiniteSets

CONSTANTS 
    MaxDataValue  \* The maximum value for data

VARIABLES 
    sendBit, ackBit, recvBit, sendData, recvData

Init == 
    /\ sendBit = FALSE 
    /\ ackBit = FALSE 
    /\ recvBit = FALSE 
    /\ sendData \in 0..MaxDataValue
    /\ recvData \in 0..MaxDataValue

Next ==
    \/ \/ Sender sends a new value
       (/\ sendBit = ackBit
        /\ recvBit # sendBit
        /\ sendData' \in 0..MaxDataValue 
        /\ sendData' # sendData
        /\ sendBit' = ~sendBit
        /\ UNCHANGED <<ackBit, recvBit, recvData>>)
    \/ \/ Receiver accepts a message
       (/\ recvBit # sendBit
        /\ recvData' = sendData
        /\ recvBit' = ~recvBit
        /\ UNCHANGED <<sendBit, ackBit, sendData>>)
    \/ \/ Sender receives an acknowledgement
       (/\ ackBit # recvBit
        /\ ackBit' = ~ackBit
        /\ UNCHANGED <<sendBit, recvBit, sendData, recvData>>)

TypeInvariant ==
    /\ sendBit \in {TRUE, FALSE}
    /\ ackBit \in {TRUE, FALSE}
    /\ recvBit \in {TRUE, FALSE}
    /\ sendData \in 0..MaxDataValue
    /\ recvData \in 0..MaxDataValue

Spec ==
    INIT Init
    /\ NEXT Next
    /\ INVARIANT TypeInvariant
    /\ SF_RecvMessage: <<recvBit # sendBit>> \<<(recvData' = sendData)>>
    /\ SF_Acknowledge: <<ackBit # recvBit>> \<<ackBit' = ~ackBit>>
    /\ <>[] (sendBit # ackBit)

====

```