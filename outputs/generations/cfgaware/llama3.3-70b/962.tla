```
MODULE ABCSpec
VARIABLES senderBit, receiverBit, sentData, receivedData, senderAckBit, receiverAckBit

TypeInv == 
  /\ senderBit \in {0, 1}
  /\ receiverBit \in {0, 1}
  /\ sentData \in {0, 1}
  /\ receivedData \in {0, 1}
  /\ senderAckBit \in {0, 1}
  /\ receiverAckBit \in {0, 1}

Init == 
  /\ senderBit = 0
  /\ receiverBit = 0
  /\ sentData = 0
  /\ receivedData = 0
  /\ senderAckBit = 0
  /\ receiverAckBit = 0

Next == 
  \/ (senderBit = senderAckBit) /\ (sentData' = sentData + 1) /\ (receiverBit' = receiverBit) /\ (receivedData' = receivedData) /\ (senderAckBit' = senderAckBit) /\ (receiverAckBit' = receiverAckBit)
  \/ (receiverBit # senderBit) /\ (senderBit' = senderBit) /\ (sentData' = sentData) /\ (receivedData' = sentData) /\ (senderAckBit' = senderAckBit) /\ (receiverAckBit' = receiverAckBit + 1)
  \/ (receiverAckBit # senderAckBit) /\ (senderBit' = senderBit) /\ (sentData' = sentData) /\ (receivedData' = receivedData) /\ (senderAckBit' = senderAckBit + 1) /\ (receiverAckBit' = receiverAckBit)

Spec == Init /\ [][Next]_<<senderBit, receiverBit, sentData, receivedData, senderAckBit, receiverAckBit>>
Fairness == 
  WF_<<senderBit, receiverBit, sentData, receivedData, senderAckBit, receiverAckBit>>(receiverBit # senderBit)
  WF_<<senderBit, receiverBit, sentData, receivedData, senderAckBit, receiverAckBit>>(receiverAckBit # senderAckBit)

THEOREM Spec => []<> (senderBit # senderAckBit)
```