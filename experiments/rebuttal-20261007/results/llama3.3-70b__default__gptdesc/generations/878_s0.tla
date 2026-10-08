```
MODULE RootedSpanningTree
EXTENDS Integers, FiniteSets

CONSTANTS Nodes, Root, MaxCardinality
VARIABLES mom, dist

Init ==
  /\ mom = [n \in Nodes |-> n]
  /\ dist = [n \in Nodes |-> IF n = Root THEN 0 ELSE MaxCardinality]

Next ==
  \E n \in Nodes, m \in Nodes :
    /\ dist[m] < dist[n]
    /\ {m, n} \subseteq Nodes
    /\ mom' = [mom EXCEPT ![n] = m]
    /\ dist' = [dist EXCEPT ![n] = (dist[n] - 1)]

Spec ==
  Init /\ [][Next]_<<mom, dist>>
 WF_<<mom, dist>>(Next)

TerminationImpliesPostcondition ==
  []<>(\A n \in Nodes : mom[n] = Root) => 
    (\A n \in Nodes : 
      /\ mom[n] \in Nodes
      /\ IF n = Root THEN mom[n] = n ELSE mom[n] /= n
      /\ dist[n] = IF n = Root THEN 0 ELSE (1 + dist[mom[n]])
      )

EventualTermination ==
  <>(\A n \in Nodes : mom[n] = Root)

EveryNodeEventuallyHasRootAsParent ==
  \A n \in Nodes : <>[]mom[n] = Root

THEOREM Spec => []TerminationImpliesPostcondition
THEOREM Spec => EventualTermination
THEOREM Spec => EveryNodeEventuallyHasRootAsParent
```