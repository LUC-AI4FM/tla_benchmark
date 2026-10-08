```
MODULE RootedSpanningTree
EXTENDS Integers, FiniteSets

CONSTANTS Nodes, Root, MaxCardinality
VARIABLES mom, dist

Init ==
  /\ mom = [n \in Nodes |-> n]
  /\ dist = [Root |-> 0] \cup [n \in (Nodes \ {Root}) |-> MaxCardinality]

Next ==
  \E n \in Nodes, p \in Nodes :
    /\ dist[n] > dist[p]
    /\ {n, p} \subseteq Nodes
    /\ mom' = [mom EXCEPT ![n] = p]
    /\ dist' = [dist EXCEPT ![n] = (dist[n] - 1)]

Spec == Init /\ [][Next]_<<mom, dist>>
          /\ WF_<<mom, dist>>(Next)

Termination ==
  <>(\A n \in Nodes : mom[n] = Root)

SafetyInvariant ==
  [](Termination => \A n \in Nodes : 
    /\ mom[n] \in Nodes
    /\ (n = Root) <=> (mom[n] = n)
    /\ \E p_1, ..., p_k \in Nodes :
        /\ p_1 = n
        /\ p_k = Root
        /\ \A i \in 1..(k-1) : 
            /\ {p_i, p_(i+1)} \subseteq Nodes
            /\ mom[p_i] = p_(i+1)
  )

Liveness == <>Termination

TemporalProperty ==
  []<><n \in Nodes : mom[n] = Root>

THEOREM Spec => []SafetyInvariant
THEOREM Spec => Liveness
THEOREM Spec => TemporalProperty
```