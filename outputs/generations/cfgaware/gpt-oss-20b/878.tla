------------------------------ MODULE RootedSpanningTree ------------------------------
EXTENDS Naturals, TemporalOperators

CONSTANTS Nodes, Root, MaxCardinality, Adj

VARIABLES mom, dist

(* Initial state *)
Init ==
    /\ mom = [i \in Nodes |-> i]
    /\ dist = [i \in Nodes |
                IF i = Root THEN 0
                ELSE MaxCardinality]

(* Type correctness *)
TypeOK ==
    /\ mom \in [Nodes -> Nodes]
    /\ dist \in [Nodes -> Nat]
    /\ \A i \in Nodes : dist[i] <= MaxCardinality
    /\ Adj \in [Nodes -> SUBSET Nodes]
    /\ \A i \in Nodes : Adj[i] \subseteq Nodes \ {i}
    /\ \A i, j \in Nodes : (j \in Adj[i]) <=> (i \in Adj[j])

(* Termination condition *)
Terminated ==
    \A i \in Nodes :
        \A j \in Adj[i] : dist[i] <= dist[j]

(* Correct tree postcondition *)
CorrectTree ==
    /\ dist[Root] = 0
    /\ mom[Root] = Root
    /\ \A i \in Nodes :
          (i # Root) => (
              mom[i] \in Adj[i]
              /\ dist[i] = dist[mom[i]] + 1)

(* Next action *)
Next ==
    \E i \in Nodes, j \in Adj[i] :
        /\ dist[j] < dist[i]
        /\ LET newDist == CHOOSE k \in Nat : (dist[j] + 1) <= k /\ k < dist[i] IN
           /\ mom' = [mom EXCEPT ![i] = j]
           /\ dist' = [dist EXCEPT ![i] = newDist]

(* Specification with weak fairness on Next *)
Spec == Init /\ WF_vars(Next)

(* Liveness property: eventual termination *)
Liveness == ◇ Terminated

(* Safety property: termination implies correct tree *)
Safety == □ (Terminated => CorrectTree)

(* Additional temporal property: every node eventually has root as parent *)
AllNodesEventuallyRootParent ==
    \A i \in Nodes : ◇ (mom[i] = Root)

=============================================================================