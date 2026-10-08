```
MODULE Paxos
EXTENDS Integers, FiniteSets

CONSTANTS Proposers, Acceptors, Values
VARIABLES sentMessages, decision, highestBallotSeen, highestBallotAccepted, acceptedValue

Init == (
  sentMessages = {}
  /\ decision = NULL
  /\ highestBallotSeen = [i \in Acceptors |-> 0]
  /\ highestBallotAccepted = [i \in Acceptors |-> 0]
  /\ acceptedValue = [i \in Acceptors |-> NULL]
)

Next == (
  \/ \E p \in Proposers, v \in Values :
    (* Send prepare message *)
    sentMessages' = sentMessages \cup {<<p, "prepare", v>>}
    /\ decision' = decision
    /\ highestBallotSeen' = highestBallotSeen
    /\ highestBallotAccepted' = highestBallotAccepted
    /\ acceptedValue' = acceptedValue
  \/ \E a \in Acceptors, p \in Proposers, v \in Values :
    (* Send promise message *)
    sentMessages' = sentMessages \cup {<<a, "promise", v>>}
    /\ decision' = decision
    /\ highestBallotSeen' = [highestBallotSeen EXCEPT ![a] = (1 + highestBallotSeen[a])]
    /\ highestBallotAccepted' = highestBallotAccepted
    /\ acceptedValue' = acceptedValue
  \/ \E p \in Proposers, v \in Values :
    (* Send accept message *)
    sentMessages' = sentMessages \cup {<<p, "accept", v>>}
    /\ decision' = decision
    /\ highestBallotSeen' = highestBallotSeen
    /\ highestBallotAccepted' = [i \in Acceptors |-> IF i = p THEN (1 + highestBallotAccepted[i]) ELSE highestBallotAccepted[i]]
    /\ acceptedValue' = [i \in Acceptors |-> IF i = p THEN v ELSE acceptedValue[i]]
  \/ \E a \in Acceptors, v \in Values :
    (* Send accepted message *)
    sentMessages' = sentMessages \cup {<<a, "accepted", v>>}
    /\ decision' = decision
    /\ highestBallotSeen' = highestBallotSeen
    /\ highestBallotAccepted' = highestBallotAccepted
    /\ acceptedValue' = [i \in Acceptors |-> IF i = a THEN v ELSE acceptedValue[i]]
  \/ \E p \in Proposers, v \in Values :
    (* Send decide message *)
    sentMessages' = sentMessages \cup {<<p, "decide", v>>}
    /\ decision' = v
    /\ highestBallotSeen' = highestBallotSeen
    /\ highestBallotAccepted' = highestBallotAccepted
    /\ acceptedValue' = acceptedValue
)

TypeCorrectness == (
  sentMessages \subseteq (Proposers \cup Acceptors) \times {"prepare", "promise", "accept", "accepted", "decide"} \times Values
  /\ decision \in Values \cup {NULL}
  /\ highestBallotSeen \in [Acceptors -> Nat]
  /\ highestBallotAccepted \in [Acceptors -> Nat]
  /\ acceptedValue \in [Acceptors -> (Values \cup {NULL})]
)

NonTriviality == (
  decision \in Values \cup {NULL}
  /\ (decision # NULL) => (decision \in {v \in Values : \E p \in Proposers : <<p, "prepare", v>> \in sentMessages})
)

Consistency == (
  [](decision # NULL) => []<>(\A a \in Acceptors : acceptedValue[a] = decision)
)

Spec == (
  Init /\ [][Next]_<<sentMessages, decision, highestBallotSeen, highestBallotAccepted, acceptedValue>>
  /\ <>FALSE (* liveness = FALSE *)
)

THEOREM Spec => []TypeCorrectness
THEOREM Spec => []NonTriviality
THEOREM Spec => Consistency
```