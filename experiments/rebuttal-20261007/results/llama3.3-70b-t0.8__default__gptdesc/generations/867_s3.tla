```
MODULE Paxos
EXTENDS Integers, FiniteSets

CONSTANTS Proposers, Acceptors, Values
VARIABLES sentMessages,
          decision,
          highestSeenBallot,
          highestAcceptedBallot,
          acceptedValue

Init ==
  /\ sentMessages = {}
  /\ decision = nil
  /\ highestSeenBallot = [i \in Acceptors |-> 0]
  /\ highestAcceptedBallot = [i \in Acceptors |-> 0]
  /\ acceptedValue = [i \in Acceptors |-> nil]

Next ==
  \/ \E p \in Proposers, v \in Values :
      /\ sentMessages' = sentMessages \cup {<<"prepare", p, v>>}
      /\ decision' = decision
      /\ highestSeenBallot' = highestSeenBallot
      /\ highestAcceptedBallot' = highestAcceptedBallot
      /\ acceptedValue' = acceptedValue
  \/ \E a \in Acceptors, b \in Nat, p \in Proposers :
      /\ sentMessages' = sentMessages \cup {<<"promise", a, b, p>>}
      /\ decision' = decision
      /\ highestSeenBallot' = [highestSeenBallot EXCEPT ![a] = b]
      /\ highestAcceptedBallot' = highestAcceptedBallot
      /\ acceptedValue' = acceptedValue
  \/ \E a \in Acceptors, b \in Nat, v \in Values :
      /\ sentMessages' = sentMessages \cup {<<"accept", a, b, v>>}
      /\ decision' = decision
      /\ highestSeenBallot' = highestSeenBallot
      /\ highestAcceptedBallot' = [highestAcceptedBallot EXCEPT ![a] = b]
      /\ acceptedValue' = [acceptedValue EXCEPT ![a] = v]
  \/ \E a \in Acceptors, b \in Nat, v \in Values :
      /\ sentMessages' = sentMessages \cup {<<"accepted", a, b, v>>}
      /\ decision' = decision
      /\ highestSeenBallot' = highestSeenBallot
      /\ highestAcceptedBallot' = highestAcceptedBallot
      /\ acceptedValue' = acceptedValue
  \/ \E v \in Values :
      /\ sentMessages' = sentMessages \cup {<<"decide", v>>}
      /\ decision' = v
      /\ highestSeenBallot' = highestSeenBallot
      /\ highestAcceptedBallot' = highestAcceptedBallot
      /\ acceptedValue' = acceptedValue

Spec ==
  /\ Init
  /\ [][Next]_<<sentMessages, decision, highestSeenBallot, highestAcceptedBallot, acceptedValue>>
  /\ WF_<<sentMessages, decision, highestSeenBallot, highestAcceptedBallot, acceptedValue>>(Next)
  /\ decision \in Values \cup {nil}
  /\ highestSeenBallot \in [Acceptors -> Nat]
  /\ highestAcceptedBallot \in [Acceptors -> Nat]
  /\ acceptedValue \in [Acceptors -> Values \cup {nil}]
  /\ sentMessages \subseteq <<<<"prepare", Proposers, Values>>>> \cup 
                   <<<<"promise", Acceptors, Nat, Proposers>>>> \cup
                   <<<<"accept", Acceptors, Nat, Values>>>> \cup
                   <<<<"accepted", Acceptors, Nat, Values>>>> \cup
                   <<<<"decide", Values>>>

THEOREM Spec => []~(decision \in Values)
THEOREM Spec => [](decision = nil \/ decision \in Values)

Liveness == FALSE

(* 
  Note: Paxos does not guarantee termination under the asynchronous fault model implied by FLP-style reasoning.
*)
```