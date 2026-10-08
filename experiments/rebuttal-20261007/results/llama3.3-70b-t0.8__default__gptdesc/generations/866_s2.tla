```
MODULE FastPaxos
EXTENDS Integers, Sequences

CONSTANTS Agents, Quorums, Values
VARIABLES state, round, value, votes

Init ==
  /\ state = [i \in Agents |-> "initial"]
  /\ round = [i \in Agents |-> 0]
  /\ value = [i \in Agents |-> nil]
  /\ votes = [r \in Nat |-> {}]

Next ==
  \/ \E a \in Agents :
    /\ state[a] = "initial"
    /\ state' = [state EXCEPT ![a] = "proposing"]
    /\ round' = round
    /\ value' = value
    /\ votes' = votes
  \/ \E a \in Agents, v \in Values :
    /\ state[a] = "proposing"
    /\ round[a] > 0
    /\ value[a] = v
    /\ votes[round[a]] = {}
    /\ votes' = [votes EXCEPT ![round[a]] = {a}]
    /\ state' = [state EXCEPT ![a] = "voting"]
    /\ round' = round
    /\ value' = value
  \/ \E a \in Agents, r \in Nat :
    /\ state[a] = "voting"
    /\ round[a] = r
    /\ Cardinality(votes[r]) >= Cardinality(Quorums[r])
    /\ \E v \in Values : 
      /\ \A q \in Quorums[r] : votes[r] \cap q /= {}
      /\ value' = [value EXCEPT ![a] = v]
    /\ state' = [state EXCEPT ![a] = "decided"]
    /\ round' = round
    /\ votes' = votes

Spec ==
  /\ Init
  /\ [][Next]_<<state, round, value, votes>>
  /\ WF_<<state, round, value, votes>>(Next)
  /\ \A a \in Agents : 
      state[a] = "decided" => \E v \in Values : value[a] = v

TypeInvariant ==
  /\ state \in [Agents |-> {"initial", "proposing", "voting", "decided"}]
  /\ round \in [Agents |-> Nat]
  /\ value \in [Agents |-> (Values \cup {nil})]
  /\ votes \in [Nat |-> SUBSET Agents]

NonTriviality ==
  /\ \A a \in Agents : state[a] = "decided" => \E v \in Values : value[a] = v
  /\ \A r \in Nat, q \in Quorums[r] : 
      Cardinality(votes[r]) >= Cardinality(q) => votes[r] \cap q /= {}

THEOREM Spec => []NonTriviality
```