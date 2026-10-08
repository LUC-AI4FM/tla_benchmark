------------------------------- MODULE AlternatingBitProtocol -------------------------------
EXTENDS Integers, TLC

CONSTANTS DataValues

VARIABLES sendBit, ackBit, recvBit, sentData, receivedData

Init == /\ sendBit = 0 
        /\ ackBit = 0 
        /\ recvBit = 0 
        /\ sentData \in DataValues
        /\ receivedData \in DataValues

Next == \/ /\ sendBit = ackBit 
            /\ \/ sentData' = sentData 
               \/ sentData' \in DataValues 
            /\ recvBit' = recvBit 
            /\ ackBit' = ackBit 
            /\ sendBit' = 1 - sendBit
        \/ /\ sendBit # recvBit 
           /\ receivedData' = sentData 
           /\ recvBit' = 1 - recvBit 
           /\ ackBit' = ackBit 
           /\ sendBit' = sendBit
        \/ /\ recvBit # ackBit 
           /\ ackBit' = recvBit 
           /\ recvBit' = recvBit 
           /\ sentData' = sentData 
           /\ sendBit' = sendBit

TypeInvariant == /\ sendBit \in {0, 1}
                 /\ ackBit \in {0, 1}
                 /\ recvBit \in {0, 1}
                 /\ sentData \in DataValues
                 /\ receivedData \in DataValues

Spec == Init /\ [][Next]_<<sendBit, ackBit, recvBit, sentData, receivedData>> /\ TypeInvariant

\* Fairness assumptions
WF_recv == WF_next(recvBit)
WF_ack == WF_next(ackBit)

\* Temporal property
OutofSyncInfinitelyOften == <>[] sendBit # ackBit

THEOREM Spec => WF_recv
THEOREM Spec => WF_ack
THEOREM Spec => OutofSyncInfinitelyOften
=============================================================================