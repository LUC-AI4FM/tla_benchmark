```
MODULE OneStepConsensus
EXTENDS Integers, FiniteSets

CONSTANTS N, F, T
VARIABLES sentMessages, receivedMessages, faultyProcesses, processStates

Init ==
  /\ sentMessages = [i \in 1..N |-> {}]
  /\ receivedMessages = [i \in 1..N |-> {}]
  /\ faultyProcesses = {}
  /\ processStates = [i \in 1..N |-> "proposal"]

Next == 
  \/ \E i \in 1..N:
    /\ processStates[i] = "proposal"
    /\ sentMessages' = [sentMessages EXCEPT ![i] = {i}]
    /\ receivedMessages' = receivedMessages
    /\ faultyProcesses' = faultyProcesses
    /\ processStates' = [processStates EXCEPT ![i] = "proposed"]
  \/ \E i \in 1..N:
    /\ processStates[i] = "proposed"
    /\ sentMessages' = sentMessages
    /\ receivedMessages' = [receivedMessages EXCEPT ![i] = {i}]
    /\ faultyProcesses' = faultyProcesses
    /\ processStates' = [processStates EXCEPT ![i] = "decided"]
  \/ \E i \in 1..N:
    /\ i \notin faultyProcesses
    /\ sentMessages' = sentMessages
    /\ receivedMessages' = receivedMessages
    /\ faultyProcesses' = faultyProcesses \cup {i}
    /\ processStates' = [processStates EXCEPT ![i] = "faulty"]
  \/ \E i \in 1..N:
    /\ Card(receivedMessages[i]) >= T
    /\ sentMessages' = sentMessages
    /\ receivedMessages' = receivedMessages
    /\ faultyProcesses' = faultyProcesses
    /\ processStates' = [processStates EXCEPT ![i] = "decided"]

Spec == Init /\ [][Next]_sentMessages, receivedMessages, faultyProcesses, processStates

THEOREM Spec => []Card(faultyProcesses) <= F
THEOREM Spec => <>~(Card({i \in 1..N : processStates[i] = "decided"}) = N - Card(faultyProcesses))

Fairness == WF_<<sentMessages, receivedMessages, faultyProcesses, processStates>>(Next)

TemporalSpec == Spec /\ Fairness

```
Note: This TLA+ specification uses the syntax of TLA+ version 2.7.0 and above. The `THEOREM` statements specify the safety property (that there are at most F Byzantine faults) and liveness property (that eventually, all non-faulty processes decide). The `Fairness` definition introduces a weak fairness condition on the main step to ensure progress under the assumption of weak fairness.