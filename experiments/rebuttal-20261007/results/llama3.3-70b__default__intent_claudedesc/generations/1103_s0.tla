```
MODULE NBAC
EXTENDS Integers, FiniteSets

CONSTANTS N, Votes
VARIABLES votes, received, decided, crashed, failureDetector

Init ==
  /\ votes \in [1..N -> {"YES", "NO"}]
  /\ received = [i \in 1..N |-> {}]
  /\ decided = [i \in 1..N |-> NULL]
  /\ crashed = {}
  /\ failureDetector \in [1..N |-> {"crashed", "all-correct"}]

Next ==
  \/ \E i \in 1..N :
    /\ ~ (i \in crashed)
    /\ votes[i] = "YES"
    /\ received[i] = {}
    /\ decided[i] = NULL
    /\ failureDetector[i] = "all-correct"
    /\ received' = [received EXCEPT ![i] = {}]
    /\ votes' = votes
    /\ decided' = decided
    /\ crashed' = crashed
    /\ failureDetector' = [failureDetector EXCEPT ![i] = "crashed"]
  \/ \E i \in 1..N :
    /\ ~ (i \in crashed)
    /\ votes[i] = "NO"
    /\ received[i] = {}
    /\ decided[i] = NULL
    /\ failureDetector[i] = "crashed"
    /\ received' = [received EXCEPT ![i] = {}]
    /\ votes' = votes
    /\ decided' = [decided EXCEPT ![i] = "ABORT"]
    /\ crashed' = crashed
    /\ failureDetector' = failureDetector
  \/ \E i \in 1..N :
    /\ ~ (i \in crashed)
    /\ received[i] # {}
    /\ \E j \in received[i] : votes[j] = "NO"
    /\ decided[i] = NULL
    /\ failureDetector[i] = "crashed"
    /\ received' = received
    /\ votes' = votes
    /\ decided' = [decided EXCEPT ![i] = "ABORT"]
    /\ crashed' = crashed
    /\ failureDetector' = failureDetector
  \/ \E i \in 1..N :
    /\ ~ (i \in crashed)
    /\ received[i] = {j \in 1..N : votes[j] = "YES"}
    /\ decided[i] = NULL
    /\ failureDetector[i] = "all-correct"
    /\ received' = received
    /\ votes' = votes
    /\ decided' = [decided EXCEPT ![i] = "COMMIT"]
    /\ crashed' = crashed
    /\ failureDetector' = failureDetector
  \/ \E i \in 1..N :
    /\ ~ (i \in crashed)
    /\ received[i] # {}
    /\ failureDetector[i] = "crashed"
    /\ decided[i] = NULL
    /\ received' = received
    /\ votes' = votes
    /\ decided' = [decided EXCEPT ![i] = "ABORT"]
    /\ crashed' = crashed
    /\ failureDetector' = failureDetector

Spec == Init /\ [][Next]_votes /\ [][Next]_received /\ [][Next]_decided /\ [][Next]_crashed /\ [][Next]_failureDetector

THEOREM Spec => []\A i \in 1..N : (decided[i] = "COMMIT") => \A j \in 1..N : votes[j] = "YES"
THEOREM Spec => []\A i \in 1..N : (votes[i] = "NO") => \A j \in 1..N : decided[j] # "COMMIT"

Fairness == WF_vars(Next, votes, received, decided, crashed, failureDetector)
```
Note: The `WF_vars` operator is used to specify weak fairness for the variables. This ensures that non-crashed processes that can vote or decide will eventually do so.