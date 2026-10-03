---------------------------- MODULE RootedSpanningTree ----------------------------
EXTENDS Integers, FiniteSets

CONSTANT Nodes, root
VARIABLE mom, dist

TypeOK == (-1 \notin Nodes) /\ (root \in Nodes) /\ 
          (* mom and dist are functions *)
          (mom \in [Nodes -> Nodes]) /\ (dist \in [Nodes -> Int])

(* Initial condition: every node points to itself, the root has distance 0, 
   and all other nodes have distance MaxCardinality *)
Init == (/\
    mom = [n \in Nodes |-> n]
    /\ dist = [n \in Nodes |-> IF n = root THEN 0 ELSE MaxCardinality]

(* Choose a node and a neighbor with a shorter distance, decrease the node's 
   distance to an arbitrary intermediate value while updating its parent *)
Next == (\E n \in Nodes, p \in Nodes : 
            /\ dist[n] > dist[p]
            /\ {n, p} \subseteq Nodes
            /\ mom' = [mom EXCEPT ![n] = p]
            /\ dist' = [dist EXCEPT ![n] = (dist[n] - 1)]

(* Termination implies a postcondition characterizing a correct rooted spanning tree *)
Safety == []<>(\A n \in Nodes : 
                /\ mom[n] \in Nodes
                /\ IF n = root THEN mom[n] = n ELSE mom[n] /= n
                /\ dist[n] >= 0
                /\ (n = root) \/ (dist[mom[n]] < dist[n]))

(* Eventual termination *)
Liveness == <>[]<>(Next)

(* Every node eventually has the root as its parent *)
EventualRootParent == []<>(\A n \in Nodes : mom[n] = root)

Spec == Init /\ [][Next]_<<mom, dist>> /\ WF_<<mom, dist>>(Next)
=============================================================================