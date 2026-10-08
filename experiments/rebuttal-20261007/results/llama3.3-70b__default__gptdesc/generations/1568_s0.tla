```
MODULE Bakery
EXTENDS Integers, FiniteSets

CONSTANTS NumProcs, MaxTicket

VARIABLES state, ticket, aux

Init ==
  /\ state \in [1..NumProcs -> {"noncritical", "waiting", "critical"}]
  /\ ticket \in [1..NumProcs -> 0..MaxTicket]
  /\ aux \in [1..NumProcs -> {}]

Next ==
  \/ \E i \in 1..NumProcs :
      /\ state[i] = "noncritical"
      /\ state' = [state EXCEPT ![i] = "waiting"]
      /\ ticket' = [ticket EXCEPT ![i] = (CHOOSE m \in Nat : m > ticket[i])]
      /\ aux' = aux
  \/ \E i \in 1..NumProcs :
      /\ state[i] = "waiting"
      /\ \A j \in 1..NumProcs : ~(state[j] = "critical" /\ (ticket[j] < ticket[i] \/ (ticket[j] = ticket[i] /\ j < i)))
      /\ state' = [state EXCEPT ![i] = "critical"]
      /\ ticket' = ticket
      /\ aux' = [aux EXCEPT ![i] = {i}]
  \/ \E i \in 1..NumProcs :
      /\ state[i] = "critical"
      /\ state' = [state EXCEPT ![i] = "noncritical"]
      /\ ticket' = [ticket EXCEPT ![i] = 0]
      /\ aux' = [aux EXCEPT ![i] = {}]

Spec ==
  Init /\ [][Next]_<<state, ticket, aux>>

MutualExclusion ==
  \A i, j \in 1..NumProcs : ~(state[i] = "critical" /\ state[j] = "critical" /\ i # j)

Fairness ==
  \A i \in 1..NumProcs :
    WF_(state[i] = "waiting") (state[i] = "critical")

THEOREM Spec => []MutualExclusion
THEOREM Spec => Fairness
```