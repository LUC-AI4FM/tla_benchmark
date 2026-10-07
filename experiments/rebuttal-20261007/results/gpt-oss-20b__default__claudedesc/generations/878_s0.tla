MODULE SpanningTree

EXTENDS Naturals, TLC

CONSTANTS
    Nodes = {"n1","n2","n3","n4","n5"},
    Edges = {{"n1","n2"}, {"n1","n3"}, {"n2","n3"}, {"n2","n4"}, {"n3","n5"}, {"n4","n5"}, {"n4","n1"}},
    Root = "n1",
    MaxCardinality = 10

ASSUME
    Root ∈ Nodes /\
    ∀ e ∈ Edges : e ⊆ Nodes /\ #e = 2 /\
    MaxCardinality ∈ Nat /\ MaxCardinality >= #Nodes

VARIABLES mom, dist

vars == <<mom, dist>>

Neighbors(n) ==
    { m \in Nodes : ∃ e ∈ Edges : n ∈ e /\ m ∈ e /\ m /= n }

EnabledNext ==
    ∃ n ∈ Nodes :
        ∃ m ∈ Neighbors(n) :
            dist[m] + 1 < dist[n]

Init ==
    (dist = [n \in Nodes |-> IF n = Root THEN 0 ELSE MaxCardinality]) /\
    (mom = [n \in Nodes |-> n])

Next ==
    ∃ n ∈ Nodes :
        ∃ m ∈ Neighbors(n) :
            dist[m] + 1 < dist[n] /\ 
            ∃ d ∈ Nat : dist[m]+1 <= d /\ d < dist[n] /\
                (dist' = [dist EXCEPT ![n] = d]) /\
                (mom' = [mom EXCEPT ![n] = m])

TypeOK ==
    mom ∈ [Nodes -> Nodes] /\ dist ∈ [Nodes -> Nat]

Unreachable(n) == dist[n] = MaxCardinality

NeighborDistMax(n) == ∀ m ∈ Neighbors(n) : dist[m] = MaxCardinality

RootCond == (dist[Root] = 0 /\ mom[Root] = Root)

ReachableCond(n) ==
    ¬Unreachable(n) => (dist[n] = dist[mom[n]] + 1 /\ mom[n] ∈ Neighbors(n))

UnreachCond(n) ==
    Unreachable(n) => (mom[n] = n /\ NeighborDistMax(n))

PostCond ==
    RootCond /\
    ∀ n ∈ Nodes \ {Root} : (UnreachCond(n) \/ ReachableCond(n))

Safety == [] (¬EnabledNext => PostCond)

Liveness == <> ¬EnabledNext

Spec == Init /\ [][Next]_vars /\ WF_Next

END MODULE