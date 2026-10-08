```
MODULE Channel
EXTENDS Integers, FiniteSets

CONSTANTS Data
VARIABLES value, ready, ack

Init == (value \in Data) /\ (ready = 0) /\ (ack = 0)

Next == 
  \/ (\E d \in Data : (ready = ack) /\ (value' = d) /\ (ready' = 1 - ready) /\ (ack' = ack))
  \/ ((ready # ack) /\ (value' = value) /\ (ready' = ready) /\ (ack' = ready))

Spec == Init /\ [][Next]_<<value, ready, ack>>

THEOREM Spec => []((ready = ack) <=> (value \in Data))
THEOREM Spec => []((ready # ack) => (value \in Data))
THEOREM Spec => <>[]((ready = ack) /\ (value \in Data))

WF1 == <>(ready # ack)
SF1 == [](ready # ack => <>[](ready = ack))

THEOREM Spec => WF1_S
THEOREM Spec => SF1_S

INV1 == []((value \in Data) /\ (ready \in {0, 1}) /\ (ack \in {0, 1}))
INV2 == []((ready = ack) <=> ((value' = value) \/ (value' \in Data)))

THEOREM Spec => INV1
THEOREM Spec => INV2

FAIRNESS <<ready, ack>>
```
Note: The above TLA+ specification models the described system. It includes the necessary variables, initialization condition, next-state relation, and invariants to capture the behavior of a single-message asynchronous unreliable channel with handshake semantics between a sender and a receiver.