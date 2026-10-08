------------------------------- MODULE ShortestPathSpanningTree -------------------------------

CONSTANTS Nodes, Root, INFINITY

VARIABLES parent, distance

ASSUME Root \in Nodes
ASSUME /\ INFINITY > 0
       /\ \A n \in Nodes : n = Root \/ INFINITY \notin {distance[n]}

Init == /\ parent = [n \in Nodes |-> n]
        /\ distance = [n \in Nodes |-> IF n = Root THEN 0 ELSE INFINITY]

Next ==
    \E n \in Nodes, m \in Nodes :
        /\ m \in Neighbors(n)
        /\ distance[m] < distance[n]
        /\ parent' = [parent EXCEPT ![n] = m]
        /\ distance' = [distance EXCEPT ![n] = distance[m] + 1]

Neighbors(node) == {m \in Nodes : <<node, m>> \in Edges \/ <<m, node>> \in Edges}

Spec ==
    /\ Init
    /\ WF_vars(Next)
    /\ SF_vars(Next)

WF_vars(action) == \A s \in State: action(s) => EnabledVars(action)(s)

SF_vars(action) == \A s \in State: action(s) => ActionEnabled(action)(s)

State == [parent : [Nodes -> Nodes], distance : [Nodes -> Nat]]

EnabledVars(action) ==
    LAMBDA s :
        LET parent' = [parent EXCEPT ![n] = m],
            distance' = [distance EXCEPT ![n] = distance[m] + 1]
        IN /\ n \in Nodes
           /\ m \in Neighbors(n)
           /\ distance[m] < distance[n]

ActionEnabled(action) ==
    LAMBDA s :
        LET parent' = [parent EXCEPT ![n] = m],
            distance' = [distance EXCEPT ![n] = distance[m] + 1]
        IN /\ n \in Nodes
           /\ m \in Neighbors(n)
           /\ distance[m] < distance[n]

TypeOK ==
    /\ parent \in [Nodes -> Nodes]
    /\ distance \in [Nodes -> Nat \/ {INFINITY}]
    /\ \A n \in Nodes : (distance[n] = INFINITY => parent[n] = n)

Safety ==
    /\ TypeOK
    /\ \A n \in Nodes :
        /\ (n = Root => /\ distance[n] = 0
                           /\ parent[n] = n)
        /\ (distance[n] > 0 =>
            /\ distance[n] = distance[parent[n]] + 1
            /\ parent[n] \in Neighbors(n))
    /\ \A n \in Nodes :
        /\ (distance[n] = INFINITY => parent[n] = n)

Liveness ==
    \A s \in State : EnabledVars(Next)(s) => <>[](EnabledVars(Next)(s))

=============================================================================