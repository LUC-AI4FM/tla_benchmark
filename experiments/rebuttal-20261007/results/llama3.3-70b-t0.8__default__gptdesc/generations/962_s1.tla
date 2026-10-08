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
  \/ (senderBit = ackBit /\ sentData' # SentData)
  \/ (receiverBit # senderBit /\ receivedData' = SentData)
  \/ (ackBit # receiverBit /\ ackBit' = receiverBit)

TypeInvariant ==
  /\ senderBit \in {0, 1}
  /\ receiverBit \in {0, 1}
  /\ sentData \in Int
  /\ receivedData \in Int

Spec ==
  Init /\ [][Next]_<<senderBit, receiverBit, sentData, receivedData, ackBit>>
  /\ WF_vars(<<receiverBit, receivedData>>)
  /\ SF_vars(<<ackBit>>)

THEOREM Spec => <>[](senderBit # ackBit)
```