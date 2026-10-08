```
MODULE AlternatingBitProtocol

EXTENDS Integers

CONSTANTS Data

VARIABLES senderBit, receiverBit, sentData, receivedData, ackBit

Init == 
  (senderBit = 0) /\ 
  (receiverBit = 0) /\ 
  (sentData = NULL) /\ 
  (receivedData = NULL) /\ 
  (ackBit = 0)

TypeInvariant == 
  (senderBit \in {0, 1}) /\ 
  (receiverBit \in {0, 1}) /\ 
  (ackBit \in {0, 1}) /\ 
  (sentData \in Data \cup {NULL}) /\ 
  (receivedData \in Data \cup {NULL})

Next == 
  \/ (\E d \in Data : 
        (senderBit = ackBit) /\ 
        (sentData' = d) /\ 
        (receiverBit' = receiverBit) /\ 
        (receivedData' = receivedData) /\ 
        (ackBit' = ackBit))
  \/ ((receiverBit # senderBit) /\ 
      (sentData =/ NULL) /\ 
      (receivedData' = sentData) /\ 
      (senderBit' = senderBit) /\ 
      (receiverBit' = receiverBit) /\ 
      (ackBit' = ackBit))
  \/ ((receiverBit # ackBit) /\ 
      (ackBit' = receiverBit) /\ 
      (senderBit' = senderBit) /\ 
      (receiverBit' = receiverBit) /\ 
      (sentData' = sentData) /\ 
      (receivedData' = receivedData))

Spec == Init /\ [][Next]_<<senderBit, receiverBit, sentData, receivedData, ackBit>>

THEOREM Spec => []TypeInvariant
THEOREM Spec => WF_(receiverBit # senderBit)(Next)
THEOREM Spec => SF_(ackBit # receiverBit)(Next)

TemporalProperty == \A s \in Nat : \E t \in (s .. Infinity) : 
  (senderBit[t] # ackBit[t])

THEOREM Spec => TemporalProperty
```