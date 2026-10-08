```
MODULE AlternatingBitProtocol

EXTENDS Integers

CONSTANTS SenderBit, ReceiverBit, SentData, ReceivedData

VARIABLES senderBit, receiverBit, sentData, receivedData, ackBit

Init == 
  /\ senderBit = 0
  /\ receiverBit = 0
  /\ sentData = 0
  /\ receivedData = 0
  /\ ackBit = 0

Next == 
  /\ (senderBit' = IF senderBit = ackBit THEN 1 - senderBit ELSE senderBit)
  /\ (receiverBit' = IF receiverBit /= senderBit THEN 1 - receiverBit ELSE receiverBit)
  /\ (sentData' \in Nat)
  /\ (receivedData' = IF receiverBit /= senderBit THEN sentData ELSE receivedData)
  /\ (ackBit' = IF receiverBit /= ackBit THEN 1 - ackBit ELSE ackBit)

TypeInvariant == 
  /\ senderBit \in {0, 1}
  /\ receiverBit \in {0, 1}
  /\ sentData \in Nat
  /\ receivedData \in Nat
  /\ ackBit \in {0, 1}

Spec == Init /\ [][Next]_<<senderBit, receiverBit, sentData, receivedData, ackBit>>
          /\ WF_<<receiverBit, senderBit>>([][(receiverBit /= senderBit) >> (receiverBit' = 1 - receiverBit)]_<<receiverBit, senderBit>>)
          /\ WF_<<ackBit, senderBit>>([][(ackBit /= senderBit) >> (ackBit' = 1 - ackBit)]_<<ackBit, senderBit>>)
          /\ []<>~(senderBit = ackBit)

THEOREM Spec => []<>~(senderBit = ackBit)
```