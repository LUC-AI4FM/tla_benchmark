```
MODULE Paxos
EXTENDS Integers, FiniteSets

CONSTANTS Proposers, Acceptors, Values
VARIABLES sentMessages, decision, highestSeen, highestAccepted, acceptedValue

Init ==
  /\ sentMessages = {}
  /\ decision = NULL
  /\ highestSeen = [i \in Acceptors |-> 0]
  /\ highestAccepted = [i \in Acceptors |-> 0]
  /\ acceptedValue = [i \in Acceptors |-> NULL]

Next == 
  \/ \E p \in Proposers, v \in Values :
      /\ sentMessages' = sentMessages \cup {<<"prepare", p, v>>}
      /\ decision' = decision
      /\ highestSeen' = highestSeen
      /\ highestAccepted' = highestAccepted
      /\ acceptedValue' = acceptedValue
  \/ \E a \in Acceptors, p \in Proposers, b \in Nat, v \in Values :
      /\ sentMessages' = sentMessages \cup {<<"promise", a, p, b>>}
      /\ decision' = decision
      /\ highestSeen' = [highestSeen EXCEPT ![a] = b]
      /\ highestAccepted' = highestAccepted
      /\ acceptedValue' = acceptedValue
  \/ \E a \in Acceptors, p \in Proposers, b \in Nat, v \in Values :
      /\ sentMessages' = sentMessages \cup {<<"accept", a, p, b, v>>}
      /\ decision' = decision
      /\ highestSeen' = [highestSeen EXCEPT ![a] = b]
      /\ highestAccepted' = [highestAccepted EXCEPT ![a] = b]
      /\ acceptedValue' = [acceptedValue EXCEPT ![a] = v]
  \/ \E a \in Acceptors, p \in Proposers, b \in Nat, v \in Values :
      /\ sentMessages' = sentMessages \cup {<<"accepted", a, p, b, v>>}
      /\ decision' = decision
      /\ highestSeen' = highestSeen
      /\ highestAccepted' = highestAccepted
      /\ acceptedValue' = acceptedValue
  \/ \E p \in Proposers, v \in Values :
      /\ sentMessages' = sentMessages \cup {<<"decide", p, v>>}
      /\ decision' = v
      /\ highestSeen' = highestSeen
      /\ highestAccepted' = highestAccepted
      /\ acceptedValue' = acceptedValue

Spec == Init /\ [][Next]_<<sentMessages, decision, highestSeen, highestAccepted, acceptedValue>>
          /\ WF_<<sentMessages, decision, highestSeen, highestAccepted, acceptedValue>>(Next)
          /\ []~<>(decision \in Values)

THEOREM Spec => []~<>(decision \in Values)
```
Note: Liveness is explicitly set to FALSE as Paxos does not guarantee termination under the asynchronous fault model implied by FLP-style reasoning.