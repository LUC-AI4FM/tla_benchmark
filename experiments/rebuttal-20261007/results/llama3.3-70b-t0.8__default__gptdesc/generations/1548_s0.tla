```
MODULE OneStepConsensus
EXTENDS Integers, TLC

CONSTANTS N, F, T, Proposal
VARIABLES sent, received, faulty, state

Init == 
  /\ sent = [i \in 1..N |-> 0]
  /\ received = [i \in 1..N |-> {}]
  /\ faulty = {}
  /\ state = [i \in 1..N |-> "propose"]

Next == 
  \/ \E i \in 1..N :
    /\ state[i] = "propose"
    /\ sent[i] < T
    /\ state' = [state EXCEPT ![i] = "send"]
    /\ sent' = [sent EXCEPT ![i] = sent[i] + 1]
    /\ received' = received
    /\ faulty' = faulty
  \/ \E i \in 1..N :
    /\ state[i] = "send"
    /\ Card(received[i]) < T
    /\ \E v \in {0, 1} : 
      /\ received' = [received EXCEPT ![i] = received[i] \cup {v}]
      /\ sent' = sent
      /\ faulty' = faulty
      /\ state' = [state EXCEPT ![i] = "receive"]
  \/ \E i \in 1..N :
    /\ state[i] = "receive"
    /\ Card(received[i]) >= T
    /\ state' = [state EXCEPT ![i] = "decide"]
    /\ sent' = sent
    /\ received' = received
    /\ faulty' = faulty
  \/ \E i \in 1..N :
    /\ i \notin faulty
    /\ faulty' = faulty \cup {i}
    /\ state' = [state EXCEPT ![i] = "faulty"]
    /\ sent' = sent
    /\ received' = received

Spec == Init /\ [][Next]_<<sent, received, faulty, state>>
  /\ WF_<<sent, received, faulty, state>>(Next)

THEOREM Spec => [](\A i, j \in 1..N : state[i] = "decide" /\ state[j] = "decide" => state[i] = state[j])
THEOREM Spec => <>(\E i \in 1..N : state[i] = "decide")

All0Init == Init /\ Proposal = 0
All1Init == Init /\ Proposal = 1

```
Note: The TLC module is extended to enable model checking with the TLA+ Toolbox. The `WF_<<sent, received, faulty, state>>(Next)` expression ensures weak fairness of the Next action. The two THEOREM statements encode safety and liveness properties. All0Init and All1Init define initial states for all-0 and all-1 proposals.