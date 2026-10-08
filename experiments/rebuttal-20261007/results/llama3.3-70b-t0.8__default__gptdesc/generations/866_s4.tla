```
MODULE FastPaxos
EXTENDS Integers, TLC

CONSTANTS Agents, Quorums, Values
VARIABLES state, round, proposal, accepted, decided

Init ==
  /\ state = [i \in Agents |-> "idle"]
  /\ round = [i \in Agents |-> 0]
  /\ proposal = [i \in Agents |-> <<>>]
  /\ accepted = [i \in Agents |-> <<>>]
  /\ decided = ""

Next == 
  \/ \E i \in Agents : 
    /\ state[i] = "idle"
    /\ round[i] < (round[j] \in Agents)
    /\ proposal[i] = << >>
    /\ state' = [state EXCEPT ![i] = "prepare"]
    /\ round' = [round EXCEPT ![i] = round[i] + 1]
    /\ UNCHANGED <<proposal, accepted, decided>>
  \/ \E i \in Agents : 
    /\ state[i] = "prepare"
    /\ \E Q \in Quorums : 
      /\ \A j \in Q : round[j] = round[i]
      /\ proposal' = [proposal EXCEPT ![i] = << >>
      /\ state' = [state EXCEPT ![i] = "accept"]
      /\ UNCHANGED <<round, accepted, decided>>
  \/ \E i \in Agents : 
    /\ state[i] = "accept"
    /\ \E v \in Values : 
      /\ \E Q \in Quorums : 
        /\ \A j \in Q : accepted[j] = <<v >>
      /\ accepted' = [accepted EXCEPT ![i] = <<v >>]
      /\ state' = [state EXCEPT ![i] = "decide"]
      /\ UNCHANGED <<round, proposal, decided>>
  \/ \E i \in Agents : 
    /\ state[i] = "decide"
    /\ \E v \in Values : 
      /\ accepted[i] = <<v >>
      /\ decided' = v
      /\ UNCHANGED <<state, round, proposal, accepted>>

Spec == Init /\ [][Next]_<<state, round, proposal, accepted, decided>>
  
TypeInvariant == 
  /\ state \in [Agents -> {"idle", "prepare", "accept", "decide"}]
  /\ round \in [Agents -> Nat]
  /\ proposal \in [Agents -> Seq(Values)]
  /\ accepted \in [Agents -> Seq(Values)]
  /\ decided \in Values \cup {""}

NonTriviality == 
  /\ \A i \in Agents : state[i] = "decide" => decided /= ""
  /\ \A v \in Values : decided = v => \E i \in Agents : accepted[i] = <<v >>
  
Fairness == 
  /\ WF_<<state, round, proposal, accepted, decided>>(Next)
  /\ SF_<<state, round, proposal, accepted, decided>>(Next)

THEOREM Spec => []NonTriviality
THEOREM Spec => Fairness
```