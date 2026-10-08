```
MODULE AlternatingBitProtocol

EXTENDS Integers

CONSTANTS SenderBit, ReceiverBit, SentData, ReceivedData

VARIABLES senderBit, receiverBit, sentData, receivedData, ackBit

Init == (
  /\ senderBit = 0
  /\ receiverBit = 0
  /\ sentData = 0
  /\ receivedData = 0
  /\ ackBit = 0
)

TypeInvariant == (
  /\ senderBit \in {0, 1}
  /\ receiverBit \in {0, 1}
  /\ sentData \in Int
  /\ receivedData \in Int
  /\ ackBit \in {0, 1}
)

Next == (
  \/ (senderBit = ackBit /\ sentData' = SentData)
  \/ (receiverBit # senderBit /\ receivedData' = sentData)
  \/ (receiverBit # ackBit /\ ackBit' = receiverBit)
)

Spec == Init /\ [][Next]_<<senderBit, receiverBit, sentData, receivedData, ackBit>>

THEOREM Spec => <>[]<>(senderBit # ackBit)
```