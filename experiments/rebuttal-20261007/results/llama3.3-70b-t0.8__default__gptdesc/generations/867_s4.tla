```
MODULE Paxos
EXTENDS Integers, Sequences

CONSTANTS Proposers, Acceptors, Values
VARIABLES sentMessages,
          decision,
          highestBallotSeen,
          highestBallotAccepted,
          acceptedValue

Init ==
  /\ sentMessages = {}
  /\ decision = NULL
  /\ highestBallotSeen = [i \in Acceptors |-> 0]
  /\ highestBallotAccepted = [i \in Acceptors |-> 0]
  /\ acceptedValue = [i \in Acceptors |-> NULL]

Next ==
  \/ \E p \in Proposers, v \in Values :
      /\ sentMessages' = sentMessages \cup {<<"prepare", p>>}
      /\ decision' = decision
      /\ highestBallotSeen' = highestBallotSeen
      /\ highestBallotAccepted' = highestBallotAccepted
      /\ acceptedValue' = acceptedValue
  \/ \E a \in Acceptors, b \in Nat, v \in Values :
      /\ sentMessages' = sentMessages \cup {<<"promise", a, b>>}
      /\ decision' = decision
      /\ highestBallotSeen' = [highestBallotSeen EXCEPT ![a] = b]
      /\ highestBallotAccepted' = highestBallotAccepted
      /\ acceptedValue' = acceptedValue
  \/ \E p \in Proposers, v \in Values :
      /\ sentMessages' = sentMessages \cup {<<"accept", p, v>>}
      /\ decision' = decision
      /\ highestBallotSeen' = highestBallotSeen
      /\ highestBallotAccepted' = highestBallotAccepted
      /\ acceptedValue' = acceptedValue
  \/ \E a \in Acceptors, b \in Nat, v \in Values :
      /\ sentMessages' = sentMessages \cup {<<"accepted", a, b, v>>}
      /\ decision' = decision
      /\ highestBallotSeen' = highestBallotSeen
      /\ highestBallotAccepted' = [highestBallotAccepted EXCEPT ![a] = b]
      /\ acceptedValue' = [acceptedValue EXCEPT ![a] = v]
  \/ \E p \in Proposers, v \in Values :
      /\ sentMessages' = sentMessages \cup {<<"decide", p, v>>}
      /\ decision' = v
      /\ highestBallotSeen' = highestBallotSeen
      /\ highestBallotAccepted' = highestBallotAccepted
      /\ acceptedValue' = acceptedValue

Spec == Init /\ [][Next]_<<sentMessages, decision, highestBallotSeen, highestBallotAccepted, acceptedValue>>
           /\ WF_<<sentMessages, decision, highestBallotSeen, highestBallotAccepted, acceptedValue>>(Next)
           /\ []~(decision \in Values)

THEOREM Spec => [](decision = NULL \/ decision \in Values)

Liveness == FALSE
```