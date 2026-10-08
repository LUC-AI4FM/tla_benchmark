```
MODULE Fischer
EXTENDS Integers, FiniteSets
CONSTANTS N, Delta, Epsilon, Infinity
VARIABLES pc, timer, critical, trying, waiting

Init ==
  /\ pc = [i \in 1..N |-> "NonCritical"]
  /\ timer = [i \in 1..N |-> Infinity]
  /\ critical = {}
  /\ trying = {}
  /\ waiting = {}

Next ==
  \/ \E i \in 1..N :
      /\ pc[i] = "NonCritical"
      /\ pc' = [pc EXCEPT ![i] = "Try"]
      /\ timer' = timer
      /\ critical' = critical
      /\ trying' = trying \cup {i}
      /\ waiting' = waiting
  \/ \E i \in 1..N :
      /\ pc[i] = "Try"
      /\ trying' = trying \ {i}
      /\ waiting' = waiting \cup {i}
      /\ critical' = critical \cup {i}
      /\ timer' = [timer EXCEPT ![i] = Delta]
      /\ pc' = [pc EXCEPT ![i] = "Critical"]
  \/ \E i \in 1..N :
      /\ pc[i] = "Critical"
      /\ timer[i] = Epsilon
      /\ critical' = critical \ {i}
      /\ trying' = trying
      /\ waiting' = waiting
      /\ timer' = [timer EXCEPT ![i] = Infinity]
      /\ pc' = [pc EXCEPT ![i] = "NonCritical"]
  \/ \E i \in 1..N :
      /\ timer[i] # Infinity
      /\ timer' = [timer EXCEPT ![i] = timer[i] - 1]
      /\ pc' = pc
      /\ critical' = critical
      /\ trying' = trying
      /\ waiting' = waiting

Spec ==
  /\ Init
  /\ [][Next]_<<pc, timer, critical, trying, waiting>>
  /\ WF_<<pc, timer, critical, trying, waiting>>(Next)

THEOREM Spec => []<>(\E i \in 1..N : pc[i] = "Critical")
```