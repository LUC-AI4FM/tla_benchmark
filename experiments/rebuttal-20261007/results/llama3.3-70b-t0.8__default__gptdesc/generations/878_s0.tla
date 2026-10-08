```
MODULE RootedSpanningTree
EXTENDS Integers, FiniteSets

CONSTANTS Nodes, Root, MaxCardinality

VARIABLES mom, dist

Init == (* Initial conditions *)
        /\ mom = [n \in Nodes |-> n]
        /\ dist = [n \in Nodes |-> IF n = Root THEN 0 ELSE MaxCardinality]

Next == (* Next state relation *)
        \E n \in Nodes, neighbor \in Nodes :
          /\ neighbor \in {m \in Nodes : m /= n}  (* Ensure neighbor is different from n *)
          /\ dist[neighbor] < dist[n]
          /\ mom' = [mom EXCEPT ![n] = neighbor]
          /\ dist' = [dist EXCEPT ![n] = (dist[n] - 1)]

Spec == Init /\ [][Next]_<<mom, dist>>
        /\ WF_<<mom, dist>>(Next)

Termination == (* Termination condition *)
               <>(\A n \in Nodes : mom[n] = Root)

Postcondition == (* Postcondition for a correct rooted spanning tree *)
                 /\ \A n \in Nodes : mom[n] = Root
                 /\ \A n \in Nodes \ {Root} :
                     \E neighbor \in Nodes :
                       /\ neighbor /= n
                       /\ dist[neighbor] < dist[n]
                       /\ mom[n] = neighbor

Safety == (* Safety property: Termination implies postcondition *)
          []<>(Termination => Postcondition)

Liveness == (* Liveness property: Eventual termination *)
            <>Termination

TemporalProperty == (* Temporal property: Every node eventually has the root as its parent *)
                   \A n \in Nodes : <>[]mom[n] = Root

THEOREM Spec => []Safety
THEOREM Spec => Liveness
THEOREM Spec => TemporalProperty
```