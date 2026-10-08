------------------------------- MODULE RandomSpanningTree -------------------------------
EXTENDS TLC, Naturals

CONSTANTS Nodes, Root, Infinity

ASSUME
    Root \in Nodes
    /\ Infinity \in Nat
    /\ Infinity > 0

VARIABLES mom, dist

Edges == [ n \in Nodes |-> RandomSubset(Nodes \ {n}) ]

Init ==
    /\ mom = [ n \in Nodes |-> n ]
    /\ dist = [ n \in Nodes |
                IF n = Root THEN 0
                ELSE Infinity ]

Next ==
    ∃ i \in Nodes :
        /\ i # Root
        /\ ∃ j \in Edges[i] :
            /\ dist[j] < dist[i]
            /\ mom' = [ mom EXCEPT ![i] = -> j ]
            /\ dist' = [ dist EXCEPT ![i] = -> dist[j] + 1 ]

TypeInv ==
    /\ mom \in [ Nodes -> Nodes ]
    /\ dist \in [ Nodes -> Nat ]
    /\ Edges \in [ Nodes -> SUBSET Nodes ]

RecDist == [ n \in Nodes |
            IF n = Root THEN 0
            ELSE IF mom[n] # n /\ dist[mom[n]] < Infinity
                THEN dist[mom[n]] + 1
                ELSE Infinity ]

PostCond == dist = RecDist

Quiescent ==
    ∀ n \in Nodes :
        ¬ (∃ j \in Edges[n] : dist[j] < dist[n])

Safety == Quiescent => PostCond

Spec ==
    Init /\ [][Next]_vars /\ WF_vars(Next) /\ TypeInv

Liveness == []<> PostCond
=============================================================================