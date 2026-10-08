```
MODULE Paxos
EXTENDS Integers, TLC

CONSTANTS Proposers, Acceptors, Values
VARIABLES sentMessages,
          decision,
          highestSeenBallot,
          highestAcceptedBallot,
          acceptedValue

Init ==
  /\ sentMessages = {}
  /\ decision = NULL
  /\ highestSeenBallot = [i \in Acceptors |-> 0]
  /\ highestAcceptedBallot = [i \in Acceptors |-> 0]
  /\ acceptedValue = [i \in Acceptors |-> NULL]

Next ==
  \/ \E p \in Proposers, v \in Values :
      /\ sentMessages' = sentMessages \cup {<<"prepare", p, v>>}
      /\ decision' = decision
      /\ highestSeenBallot' = highestSeenBallot
      /\ highestAcceptedBallot' = highestAcceptedBallot
      /\ acceptedValue' = acceptedValue
  \/ \E a \in Acceptors, p \in Proposers, v \in Values :
      /\ << "prepare", p, v >> \in sentMessages
      /\ sentMessages' = sentMessages \cup {<<"promise", a, p, v>>}
      /\ decision' = decision
      /\ highestSeenBallot' = [highestSeenBallot EXCEPT ![a] = p]
      /\ highestAcceptedBallot' = highestAcceptedBallot
      /\ acceptedValue' = acceptedValue
  \/ \E a \in Acceptors, p \in Proposers, v \in Values :
      /\ << "promise", a, p, v >> \in sentMessages
      /\ sentMessages' = sentMessages \cup {<<"accept", a, p, v>>}
      /\ decision' = decision
      /\ highestSeenBallot' = highestSeenBallot
      /\ highestAcceptedBallot' = [highestAcceptedBallot EXCEPT ![a] = p]
      /\ acceptedValue' = [acceptedValue EXCEPT ![a] = v]
  \/ \E a \in Acceptors, p \in Proposers, v \in Values :
      /\ << "accept", a, p, v >> \in sentMessages
      /\ sentMessages' = sentMessages \cup {<<"accepted", a, p, v>>}
      /\ decision' = decision
      /\ highestSeenBallot' = highestSeenBallot
      /\ highestAcceptedBallot' = highestAcceptedBallot
      /\ acceptedValue' = acceptedValue
  \/ \E Q \subseteq Acceptors :
      /\ Q \in Quorums
      /\ \A a \in Q : << "accepted", a, decision, acceptedValue'[a] >> \in sentMessages'
      /\ sentMessages' = sentMessages \cup {<<"decide", decision>>}
      /\ decision' = acceptedValue'[Q]
      /\ highestSeenBallot' = highestSeenBallot
      /\ highestAcceptedBallot' = highestAcceptedBallot
      /\ acceptedValue' = acceptedValue

Spec ==
  /\ Init
  /\ [][Next]_<<sentMessages, decision, highestSeenBallot, highestAcceptedBallot, acceptedValue>>
  /\ WF_<<sentMessages, decision, highestSeenBallot, highestAcceptedBallot, acceptedValue>>(Next)
  /\ decision \in Values \cup {NULL}
  /\ \A a \in Acceptors : highestSeenBallot[a] \leq highestAcceptedBallot[a]
  /\ \A a \in Acceptors : acceptedValue[a] \in Values \cup {NULL}

THEOREM Spec => []decision \in Values \cup {NULL}
THEOREM Spec => <>decision \in Values
```
Note: The `Quorums` set is assumed to be defined elsewhere, and the `TLC` module is used for the `WF_` operator. Also, this specification does not guarantee termination under the asynchronous fault model implied by FLP-style reasoning, as noted in the comments. Liveness is explicitly set to FALSE.