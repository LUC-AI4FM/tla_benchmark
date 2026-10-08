```
MODULE AlternatingBitProtocol

EXTENDS Integers

CONSTANTS SenderBit, ReceiverBit, SentData, ReceivedData
VARIABLES senderBit, receiverBit, sentData, receivedData, ackBit

Init == 
  (senderBit = 0) ∧ 
  (receiverBit = 0) ∧ 
  (sentData = 0) ∧ 
  (receivedData = 0) ∧ 
  (ackBit = 0)

TypeInvariant == 
  (senderBit \in {0, 1}) ∧ 
  (receiverBit \in {0, 1}) ∧ 
  (sentData \in Int) ∧ 
  (receivedData \in Int) ∧ 
  (ackBit \in {0, 1})

Next == 
  ∨ (senderBit = ackBit ∧ sentData' = SentData ∧ senderBit' = 1 - senderBit ∧ receiverBit' = receiverBit ∧ receivedData' = receivedData ∧ ackBit' = ackBit)
  ∨ (receiverBit ≠ senderBit ∧ receivedData' = sentData ∧ receiverBit' = 1 - receiverBit ∧ senderBit' = senderBit ∧ sentData' = sentData ∧ ackBit' = ackBit)
  ∨ (receiverBit ≠ ackBit ∧ ackBit' = 1 - ackBit ∧ senderBit' = senderBit ∧ receiverBit' = receiverBit ∧ sentData' = sentData ∧ receivedData' = receivedData)

Spec == Init ∧ [][Next]_<<senderBit, receiverBit, sentData, receivedData, ackBit>>
  ∧ WF_<<receiverBit, receivedData>>([][(receiverBit ≠ senderBit ∧ receivedData' = sentData)]_<<receiverBit, receivedData>>)
  ∧ SF_<<ackBit>>([][(receiverBit ≠ ackBit ∧ ackBit' = 1 - ackBit)]_<<ackBit>>)

THEOREM Spec ⇒ □⟨∃∞ t ∈ Nat : senderBit[t] ≠ ackBit[t]⟩
```