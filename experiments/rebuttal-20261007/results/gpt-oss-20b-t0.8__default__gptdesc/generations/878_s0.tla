------------------------------ MODULE SpanningTree ------------------------------
EXTENDS Naturals, TLC, Temporal

CONSTANTS
    Nodes,
    Root \in Nodes,
    Graph \subseteq Nodes × Nodes,
    MaxCardinality

ASSUME
    /\ Root ∈ Nodes
    /\ Graph ⊆ Nodes × Nodes
    /\ \A x, y \in Nodes : ((x,y) ∈ Graph) => (y,x) ∈ Graph

VARIABLES
    mom,
    dist

(* Helper definitions *)
Adj(x) == { y \in Nodes : (x, y) ∈ Graph }

Terminal ==
    \A i \in Nodes :
        ~\E j \in Adj(i) : dist[j] < dist[i]

TreeInvariant ==
    /\ mom[Root] = Root
    /\ \A i \in Nodes \ {Root} : mom[i] ∈ Adj(i)
    /\ \A i \in Nodes :
            (i = Root /\ dist[i] = 0) \/ (i # Root => dist[i] = 1 + dist[mom[i]])
    /\ \A i \in Nodes : dist[i] <= MaxCardinality
    /\ ~\E i \in Nodes \ {Root} : mom[i] = i

Init ==
    /\ mom = [i \in Nodes |-> i]
    /\ dist = [i \in Nodes |
                IF i = Root THEN 0 ELSE MaxCardinality]

Next ==
    ∃ i, j ∈ Nodes :
        /\ i # Root
        /\ j ∈ Adj(i)
        /\ dist[j] < dist[i]
        /\ ∃ d \in 0 .. dist[i]-1 :
            /\ mom' = [mom EXCEPT ![i] = j]
            /\ dist' = [dist EXCEPT ![i] = d]
    \/ UNCHANGED <<mom, dist>>

vars == <<mom, dist>>

Spec ==
    Init
    /\ [][Next]_vars
    /\ WF_vars(Next)

Safety ==
    [] (~Terminal \/ TreeInvariant)

LivenessTermination ==
    [] <> Terminal

LivenessAllRootParent ==
    \A i \in Nodes : <> (mom[i] = Root)

=============================================================================