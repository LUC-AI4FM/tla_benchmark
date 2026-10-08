---------------------------- MODULE ABCSpec ----------------------------
EXTENDS Integers, FiniteSets

CONSTANT Data
VARIABLES senderData, receiverData, sendBit, ackBit, receiverBit

TypeInv == 
  /\ senderData \in Data
  /\ receiverData \in Data
  /\ sendBit \in {0, 1}
  /\ ackBit \in {0, 1}
  /\ receiverBit \in {0, 1}

Init == 
  /\ senderData \in Data
  /\ receiverData = senderData
  /\ sendBit = 0
  /\ ackBit = 0
  /\ receiverBit = 0

Send == 
  /\ sendBit = ackBit
  /\ senderData' \in Data
  /\ sendBit' = 1 - sendBit
  /\ ackBit' = ackBit
  /\ receiverData' = receiverData
  /\ receiverBit' = receiverBit

Receive == 
  /\ receiverBit /= sendBit
  /\ receiverData' = senderData
  /\ receiverBit' = sendBit
  /\ sendBit' = sendBit
  /\ ackBit' = ackBit
  /\ senderData' = senderData

Ack == 
  /\ ackBit /= receiverBit
  /\ ackBit' = receiverBit
  /\ sendBit' = sendBit
  /\ receiverData' = receiverData
  /\ receiverBit' = receiverBit
  /\ senderData' = senderData

Next == 
  \/ Send
  \/ Receive
  \/ Ack
  \/ (sendBit' = sendBit)
    /\ (receiverData' = receiverData)
    /\ (ackBit' = ackBit)
    /\ (receiverBit' = receiverBit)
    /\ (senderData' = senderData)

Spec == 
  Init /\ [][Next]_<<senderData, receiverData, sendBit, ackBit, receiverBit>>
  /\ WF_<<receiverData, receiverBit>>(Receive)
  /\ WF_<<ackBit, receiverBit>>(Ack)

ABCSpec == Spec /\ [][TypeInv]_<<senderData, receiverData, sendBit, ackBit, receiverBit>>
=============================================================================