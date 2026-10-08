```
MODULE AlternatingBitProtocol
EXTENDS Integers, TLC

CONSTANTS Data

VARIABLES senderData, receiverData, sendBit, ackBit, receiverBit

Init ==
  /\ senderData \in Data
  /\ receiverData \in Data
  /\ sendBit \in {0, 1}
  /\ ackBit \in {0, 1}
  /\ receiverBit \in {0, 1}

TypeInvariant ==
  /\ senderData \in Data
  /\ receiverData \in Data
  /\ sendBit \in {0, 1}
  /\ ackBit \in {0, 1}
  /\ receiverBit \in {0, 1}

Send ==
  /\ sendBit = ackBit
  /\ senderData' \in Data
  /\ sendBit' = 1 - sendBit
  /\ ackBit' = ackBit
  /\ receiverData' = receiverData
  /\ receiverBit' = receiverBit

Receive ==
  /\ receiverBit # sendBit
  /\ receiverData' = senderData
  /\ receiverBit' = sendBit
  /\ sendBit' = sendBit
  /\ ackBit' = ackBit
  /\ senderData' = senderData

Ack ==
  /\ ackBit # receiverBit
  /\ ackBit' = receiverBit
  /\ sendBit' = sendBit
  /\ receiverBit' = receiverBit
  /\ receiverData' = receiverData
  /\ senderData' = senderData

Next ==
  \/ Send
  \/ Receive
  \/ Ack
  \/ (UNCHANGED <<senderData, receiverData, sendBit, ackBit, receiverBit>>)

Spec ==
  Init /\ [][Next]_<<senderData, receiverData, sendBit, ackBit, receiverBit>>
  /\ WF_<<Receive>>(Receive)
  /\ WF_<<Ack>>(Ack)

THEOREM Spec => []TypeInvariant
```