```
MODULE SpanningTreeAlgorithm

EXTENDS Integers, FiniteSets

CONSTANTS Nodes, Root
VARIABLES Distance, Parent

Init ==
  /\ Distance = [n \in Nodes |-> IF n = Root THEN 0 ELSE Cardinality(Nodes)]
  /\ Parent = [n \in Nodes |-> n]

Next ==
  \/ \E n \in Nodes :
      /\ \E m \in Nodes :
          /\ {m, n} \subseteq Nodes
          /\ m /= n
          /\ Distance[m] < Distance[n] - 1
          /\ Distance[n] > Distance[m] + 1
          /\ Distance' = [Distance EXCEPT ![n] = Distance[m] + 1]
          /\ Parent' = [Parent EXCEPT ![n] = m]
      \/ Distance' = Distance
      /\ Parent' = Parent

Spec ==
  Init /\ [][Next]_<<Distance, Parent>>

SpanningTreeInvariant ==
  \A n \in Nodes :
    IF n /= Root THEN
      (Distance[n] = Cardinality(Nodes)) \/ (\E m \in Nodes : m /= n /\ Distance[m] < Distance[n] - 1)

Termination ==
  <>(\A n \in Nodes : 
    ~(\E m \in Nodes : m /= n /\ Distance[m] < Distance[n] - 1 /\ Distance[n] > Distance[m] + 1)))

THEOREM Spec => []SpanningTreeInvariant
THEOREM Spec => Termination

Fairness == SF_VARIABLES(Distance, Parent)

=============================================================================
```