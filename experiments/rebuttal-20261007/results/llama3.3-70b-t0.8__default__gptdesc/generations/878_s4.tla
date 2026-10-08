```
MODULE RootedSpanningTree
EXTENDS Integers, FiniteSets

CONSTANTS Nodes, Root, MaxCardinality
VARIABLES mom, dist

Init == (* Initial condition *)
        /\ mom = [n \in Nodes |-> n]
        /\ dist = [n \in Nodes |-> IF n = Root THEN 0 ELSE MaxCardinality]

Next == (* Next-state relation *)
        \E n \in Nodes, m \in Nodes :
          /\ dist[n] > dist[m]
          /\ {n, m} \subseteq Nodes
          /\ mom' = [mom EXCEPT ![n] = m]
          /\ dist' = [dist EXCEPT ![n] = (dist[m] + 1)]

Spec == Init /\ [][Next]_<<mom, dist>>
        /\ WF_<<mom, dist>>(Next)

Termination == <<mom, dist>> = <<[n \in Nodes |-> Root], [n \in Nodes |-> 0]>>

SafetyProperty == []((Termination) => (
                        /\ \A n \in Nodes : mom[n] = Root
                        /\ \A n, m \in Nodes : {n, m} \subseteq Nodes => dist[n] <= dist[m] + 1
                      ))

LivenessProperty == <>Termination

TemporalProperty == []<>(\A n \in Nodes : mom[n] = Root)

THEOREM Spec => []SafetyProperty
THEOREM Spec => LivenessProperty
THEOREM Spec => TemporalProperty
```