------------------------------ MODULE AlternatingBitProtocol ------------------------------

EXTENDS Naturals, Sequences

CONSTANTS DataValues

VARIABLES sendBit, ackBit, recvBit, sendData, recvData

Init == /\ sendBit = 0 
        /\ ackBit = 0 
        /\ recvBit = 0 
        /\ sendData \in DataValues
        /\ recvData \notin DataValues

Next == \/ /\ sendBit = ackBit
             /\ recvBit # sendBit
             /\ sendData' \in DataValues
             /\ sendData' # sendData
             /\ recvData' = sendData'
             /\ sendBit' = 1 - sendBit
             /\ ackBit' = ackBit
             /\ recvBit' = recvBit
        \/ /\ sendBit # ackBit
             /\ recvBit = sendBit
             /\ sendData' = sendData
             /\ recvData' \in DataValues
             /\ sendBit' = sendBit
             /\ ackBit' = recvBit
             /\ recvBit' = 1 - recvBit
        \/ /\ sendBit = ackBit
             /\ recvBit # sendBit
             /\ sendData' = sendData
             /\ recvData' = recvData
             /\ sendBit' = sendBit
             /\ ackBit' = recvBit
             /\ recvBit' = recvBit

TypeInvariant == /\ sendBit \in {0, 1}
                 /\ ackBit \in {0, 1}
                 /\ recvBit \in {0, 1}
                 /\ sendData \in DataValues \/ sendData \notin DataValues
                 /\ recvData \in DataValues \/ recvData \notin DataValues

 fairness == WF_next(recvBit)
           /\ SF_next(ackBit)

Spec == Init /\ [][Next]_<<sendBit, ackBit, recvBit, sendData, recvData>> /\ TypeInvariant /\ fairness

Invariant == G(sendBit = ackBit => <>[]recvBit # sendBit) 

=============================================================================