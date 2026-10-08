```
MODULE FastPaxos
EXTENDS Integers, FiniteSets

CONSTANTS Agents, Quorums, Values
VARIABLES state, proposals, acceptances, coordinator

Init ==
  /\ state = [a \in Agents |-> "initial"]
  /\ proposals = [a \in Agents |-> {}]
  /\ acceptances = [a \in Agents |-> {}]
  /\ coordinator \in Agents

Next ==
  /\ IF coordinator "propose" 
    THEN 
      /\ state' = [state EXCEPT ![coordinator] = "proposed"]
      /\ proposals' = [proposals EXCEPT ![coordinator] = {coordinator}]
      /\ acceptances' = acceptances
      /\ UNCHANGED coordinator
    ELSE 
      IF \E a \in Agents : state[a] = "prepared"
        THEN 
          /\ state' = [state EXCEPT ![a] = "accepted"]
          /\ proposals' = [proposals EXCEPT ![a] = {a} \cup proposals[a]]
          /\ acceptances' = [acceptances EXCEPT ![a] = {a} \cup acceptances[a]]
          /\ UNCHANGED coordinator
        ELSE 
          /\ state' = state
          /\ proposals' = proposals
          /\ acceptances' = acceptances
          /\ UNCHANGED coordinator

Spec == Init /\ [][Next]_state /\ [][Next]_proposals /\ [][Next]_acceptances /\ [][Next]_coordinator

TypeInvariant == 
  /\ state \in [Agents -> {"initial", "prepared", "accepted", "proposed"}]
  /\ proposals \in [Agents -> SUBSET Agents]
  /\ acceptances \in [Agents -> SUBSET Agents]
  /\ coordinator \in Agents

NonTriviality == <>(\E a \in Agents : state[a] = "accepted")

Consensus == 
  (\A v \in Values : <>[]<>(\E a \in Agents : state[a] = "accepted" /\ proposals[a] = {v})) =>
    (\A v \in Values : []<>(\A a \in Agents : state[a] = "accepted" => proposals[a] = {v}))

THEOREM Spec => []TypeInvariant
THEOREM Spec => NonTriviality
THEOREM Spec => Consensus
```
Note that I've assumed the following:

* `Agents` is a set of agent identifiers.
* `Quorums` is not explicitly used in this specification, but it could be added as an additional constant if needed.
* `Values` is a set of possible proposal values.
* The `state` variable keeps track of each agent's state (initial, prepared, accepted, or proposed).
* The `proposals` and `acceptances` variables keep track of the proposals and acceptances for each agent, respectively.
* The `coordinator` variable identifies the unique coordinator agent.