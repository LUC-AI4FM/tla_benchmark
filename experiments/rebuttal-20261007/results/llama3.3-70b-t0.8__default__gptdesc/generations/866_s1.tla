```
MODULE FastPaxos
EXTENDS Integers, TLC

CONSTANTS Agents, Quorums, Values
VARIABLES state, proposals, accepted, decided

Init ==
  /\ state = [i \in Agents |-> "initial"]
  /\ proposals = [i \in Agents |-> {}]
  /\ accepted = [i \in Agents |-> {}]
  /\ decided = ""

Next == 
  \/ \E a \in Agents : 
    /\ state[a] = "initial"
    /\ state' = [state EXCEPT ![a] = "proposing"]
    /\ proposals' = [proposals EXCEPT ![a] = {a}]
    /\ accepted' = accepted
    /\ decided' = decided
  \/ \E a \in Agents, v \in Values : 
    /\ state[a] = "proposing"
    /\ proposals[a] = {a}
    /\ state' = [state EXCEPT ![a] = "waiting"]
    /\ proposals' = [proposals EXCEPT ![a] = {a, v}]
    /\ accepted' = accepted
    /\ decided' = decided
  \/ \E a \in Agents : 
    /\ state[a] = "waiting"
    /\ \E Q \in Quorums : accepted[Q] = {}
    /\ state' = [state EXCEPT ![a] = "learning"]
    /\ proposals' = proposals
    /\ accepted' = [accepted EXCEPT ![Q] = {a}]
    /\ decided' = decided
  \/ \E a \in Agents, v \in Values : 
    /\ state[a] = "learning"
    /\ \E Q \in Quorums : accepted[Q] = {a}
    /\ decided = ""
    /\ state' = [state EXCEPT ![a] = "decided"]
    /\ proposals' = proposals
    /\ accepted' = accepted
    /\ decided' = v

Spec == Init /\ [][Next]_state /\ [][Next]_proposals /\ [][Next]_accepted /\ [][Next]_decided

TypeInvariant == 
  state \in [Agents -> {"initial", "proposing", "waiting", "learning", "decided"}]
  /\ proposals \in [Agents -> SUBSET Values]
  /\ accepted \in [Quorums -> SUBSET Agents]
  /\ decided \in (Values \cup {""})

NonTriviality == decided \in Values

Consensus == 
  <>[]<>(\E v \in Values : decided = v) 

Fairness == 
  SF_VARIABLES(state, proposals, accepted, decided)

THEOREM Spec => []TypeInvariant
THEOREM Spec => NonTriviality
THEOREM Spec => Consensus
THEOREM Spec => Fairness
```