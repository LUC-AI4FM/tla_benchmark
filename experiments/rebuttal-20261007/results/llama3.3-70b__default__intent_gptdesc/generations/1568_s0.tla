```tla
MODULE BakeryAlgorithm

EXTENDS Integers, FiniteSets

CONSTANTS NumThreads, MaxTicket

VARIABLES choosing, tickets, inCS, maxObserved

Init ==
  /\ choosing = [i \in 1..NumThreads |-> FALSE]
  /\ tickets = [i \in 1..NumThreads |-> 0]
  /\ inCS = [i \in 1..NumThreads |-> FALSE]
  /\ maxObserved = [i \in 1..NumThreads |-> 0]

Next ==
  \/ \E i \in 1..NumThreads :
    /\ choosing[i] = FALSE
    /\ tickets[i] = 0
    /\ inCS[i] = FALSE
    /\ choosing' = [choosing EXCEPT ![i] = TRUE]
    /\ tickets' = tickets
    /\ inCS' = inCS
    /\ maxObserved' = maxObserved
  \/ \E i \in 1..NumThreads :
    /\ choosing[i] = TRUE
    /\ tickets[i] = 0
    /\ inCS[i] = FALSE
    /\ maxObserved' = [maxObserved EXCEPT ![i] = CHOOSE j \in 1..NumThreads : tickets[j]]
    /\ choosing' = choosing
    /\ tickets' = [tickets EXCEPT ![i] = IF maxObserved'[i] < MaxTicket THEN maxObserved'[i] + 1 ELSE MaxTicket]
    /\ inCS' = inCS
  \/ \E i \in 1..NumThreads :
    /\ choosing[i] = FALSE
    /\ tickets[i] > 0
    /\ inCS[i] = FALSE
    /\ \A j \in 1..NumThreads : ~(tickets[j] # 0 /\ (tickets[j] < tickets[i] \/ (tickets[j] = tickets[i] /\ j < i)))
    /\ choosing' = choosing
    /\ tickets' = tickets
    /\ inCS' = [inCS EXCEPT ![i] = TRUE]
    /\ maxObserved' = maxObserved
  \/ \E i \in 1..NumThreads :
    /\ choosing[i] = FALSE
    /\ tickets[i] > 0
    /\ inCS[i] = TRUE
    /\ choosing' = [choosing EXCEPT ![i] = TRUE]
    /\ tickets' = [tickets EXCEPT ![i] = 0]
    /\ inCS' = [inCS EXCEPT ![i] = FALSE]
    /\ maxObserved' = maxObserved

Spec ==
  Init /\ [][Next]_choosing, tickets, inCS, maxObserved

SafetyInvariant ==
  \A i, j \in 1..NumThreads : ~(inCS[i] /\ inCS[j] /\ i # j)

LivenessProperty ==
  \A i \in 1..NumThreads :
    WF_vars(Next, choosing, tickets, inCS, maxObserved) =>
    <> <>(inCS[i])

BoundednessInvariant ==
  \A i \in 1..NumThreads : tickets[i] <= MaxTicket

DeadlockFreedomInvariant ==
  \E i \in 1..NumThreads :
    ~(choosing[i] /\ tickets[i] = 0 /\ inCS[i] = FALSE) \/ (tickets[i] # 0 /\ \A j \in 1..NumThreads : ~(tickets[j] # 0 /\ (tickets[j] < tickets[i] \/ (tickets[j] = tickets[i] /\ j < i))))

THEOREM Spec => []SafetyInvariant
THEOREM Spec => LivenessProperty
THEOREM Spec => []BoundednessInvariant
THEOREM Spec => []DeadlockFreedomInvariant

```
Note: The `WF_vars` operator is used to express weak fairness, which means that if a thread is continuously enabled, it will eventually take a step. This is used in the liveness property to ensure that every thread that repeatedly attempts to enter the critical section will eventually enter it.