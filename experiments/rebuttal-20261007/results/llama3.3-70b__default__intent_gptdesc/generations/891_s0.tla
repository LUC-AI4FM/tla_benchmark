```
MODULE HandshakeProtocol
EXTENDS Integers, FiniteSets

CONSTANTS DataValues, SenderState, ReceiverState
VARIABLES ready, acknowledge, data, senderState, receiverState

Init ==
  /\ ready \in {0, 1}
  /\ acknowledge \in {0, 1}
  /\ data \in DataValues
  /\ senderState \in SenderState
  /\ receiverState \in ReceiverState
  /\ ready = acknowledge

Next ==
  \/ /\ ready = acknowledge
     /\ senderState \in SenderState
     /\ data' \in DataValues
     /\ ready' = 1 - ready
     /\ acknowledge' = acknowledge
     /\ senderState' = senderState
     /\ receiverState' = receiverState
  \/ /\ ready # acknowledge
     /\ receiverState \in ReceiverState
     /\ acknowledge' = ready
     /\ ready' = ready
     /\ data' = data
     /\ senderState' = senderState
     /\ receiverState' = receiverState

Spec ==
  Init /\ [][Next]_<<ready, acknowledge, data, senderState, receiverState>>

TypeInvariant ==
  ready \in {0, 1}
  /\ acknowledge \in {0, 1}
  /\ data \in DataValues
  /\ senderState \in SenderState
  /\ receiverState \in ReceiverState

DataIntegrityInvariant ==
  (ready # acknowledge) => (data = data')

DeadlockFreedom ==
  <>(ready = 1) => <> (acknowledge = 1)

HandshakeAlternationInvariant ==
  (ready # acknowledge) <=> (senderState # receiverState)

EventualAcknowledgement ==
  []<>(ready = 1) => <> (acknowledge = 1)

THEOREM Spec => []TypeInvariant
THEOREM Spec => []DataIntegrityInvariant
THEOREM Spec => DeadlockFreedom
THEOREM Spec => []HandshakeAlternationInvariant
THEOREM Spec => EventualAcknowledgement

FAIRNESS Next
```