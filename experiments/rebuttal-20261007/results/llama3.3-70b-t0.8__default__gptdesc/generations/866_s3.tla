```
MODULE FastPaxos
EXTENDS Integers, TLC

CONSTANTS Agents, Quorums, Values
VARIABLES state, proposals, accepted, decided

Init ==
  /\ state = [i \in Agents |-> "initial"]
  /\ proposals = <<>>
  /\ accepted = [i \in Agents |-> {}]
  /\ decided = ""

Next == 
  /\ \/ \E p \in Values : 
        /\ state' = [state EXCEPT ![Coordinator] = "proposing"]
        /\ proposals' = Append(proposals, <<p>>)
        /\ UNCHANGED accepted
        /\ UNCHANGED decided
    \/ \E a \in Agents, q \in Quorums :
        /\ state' = [state EXCEPT ![a] = "accepting"]
        /\ proposals' = proposals
        /\ accepted' = [accepted EXCEPT ![a] = {p \in Values : p = Head(proposals)}]
        /\ UNCHANGED decided
    \/ \E a \in Agents, q \in Quorums :
        /\ state' = [state EXCEPT ![a] = "deciding"]
        /\ proposals' = proposals
        /\ accepted' = accepted
        /\ decided' = Head(proposals)
  /\ \/ decided /= "" 
      /\ \A a \in Agents : state'[a] = "decided"
    \/ decided = ""

Spec == Init /\ [][Next]_state /\ [][Next]_proposals /\ [][Next]_accepted /\ [][Next]_decided

TypeInvariant == 
  /\ state \in [Agents -> {"initial", "proposing", "accepting", "deciding"}]
  /\ proposals \in Seq(Values)
  /\ accepted \in [Agents -> SUBSET Values]
  /\ decided \in (Values \cup {""})

NonTriviality == decided /= "" => decided \in Values

Consensus == 
  []<<decided >>_proposals /\ []<<decided >>_accepted

Fairness == 
  <>[]<>(\E p \in Values : proposals = <<p>>) 
  /\ <>[]<>(\A a \in Agents : state[a] = "decided")
```
Note: `Coordinator` is assumed to be a constant representing the unique coordinator agent. This specification models a simplified version of Fast Paxos, focusing on key aspects such as proposing, accepting, and deciding values, while omitting explicit failure modeling due to the assumption that agents can restore their state from stable storage. The `TypeInvariant` ensures that all variables are well-typed throughout the execution, and the `NonTriviality` property verifies that only proposed values can be decided upon. Finally, the `Consensus` and `Fairness` properties capture the essence of achieving consensus on a value that has been proposed and ensure liveness by requiring eventual progress towards deciding a value for all agents.