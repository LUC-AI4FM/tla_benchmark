------------------------------- MODULE AlternatingBitProtocol -------------------------------
EXTENDS Naturals, Sequences

CONSTANTS DataValues

VARIABLES sendBit, ackBit, recvBit, sendData, recvData

Init == /\ sendBit = 0 
        /\ ackBit  = 0 
        /\ recvBit = 0 
        /\ sendData \in DataValues
        /\ recvData \notin DataValues

Next == \/ /\ sendBit = ackBit 
           /\ recvBit # sendBit 
           /\ /\ sendData' \in DataValues 
              /\ sendData' # sendData 
              /\ recvData' = sendData 
              /\ ackBit'  = sendBit 
              /\ recvBit' = sendBit
        \/ /\ sendBit # ackBit 
           /\ recvBit = sendBit 
           /\ /\ sendData' = sendData 
              /\ recvData' \in DataValues 
              /\ recvData' # recvData 
              /\ ackBit'  = ackBit 
              /\ recvBit' = ackBit
        \/ /\ sendBit # ackBit 
           /\ recvBit # sendBit 
           /\ /\ sendData' = sendData 
              /\ recvData' = recvData 
              /\ ackBit'  = recvBit 
              /\ recvBit' = recvBit

TypeInvariant == /\ sendBit \in {0, 1}
                 /\ ackBit  \in {0, 1} 
                 /\ recvBit \in {0, 1} 
                 /\ sendData \in DataValues \/ sendData \notin DataValues 
                 /\ recvData \in DataValues \/ recvData \notin DataValues

Spec == Init /\ [][Next]_<<sendBit, ackBit, recvBit, sendData, recvData>> /\ WF_<<sendBit, ackBit, recvBit, sendData, recvData>>(Next)

Invariant == sendBit = ackBit \/ sendBit # recvBit

Liveness == <>[] sendBit # ackBit
=============================================================================