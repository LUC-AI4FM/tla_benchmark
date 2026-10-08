------------------------------- MODULE ShortestPathSpanningTree -------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS Nodes, Edges, Root

VARIABLES Parent, Distance

Init == /\ Parent \in [Nodes -> Nodes]
        /\ Distance \in [Nodes -> {0} \cup {omega}]
        /\ \A n \in Nodes: Parent[n] = n
        /\ Distance[Root] = 0
        /\ \A n \in Nodes \ {Root}: Distance[n] = omega

Next == \E n \in Nodes, m \in Nodes:
            \/ /\ m \in Neighbors(n)
               /\ Distance[m] < Distance[n]
               /\ Parent' = [Parent EXCEPT ![n] = m]
               /\ Distance' = [Distance EXCEPT ![n] = Distance[m] + 1]
            \/ Parent' = Parent
               /\ Distance' = Distance

Neighbors(n) == {m \in Nodes : {n, m} \in Edges}

Spec ==
    /\ Init
    /\ [][Next]_<<Parent, Distance>>
    /\ WF_next(<<Parent, Distance>>)

Safety ==
    /\ \A n \in Nodes: Parent[n] \in Neighbors(n) \/ Parent[n] = n
    /\ \A n \in Nodes: Distance[n] \in Nat \/ Distance[n] = omega
    /\ \A n \in Nodes \ {Root}: Distance[n] > 0 => Distance[n] = Distance[Parent[n]] + 1
    /\ Distance[Root] = 0
    /\ Parent[Root] = Root

Convergence ==
    \E stableState \in [Nodes -> {omega}] \X [Nodes -> Nodes]:
        \/ \A n \in Nodes: Distance'[n] = stableState[n]
           /\ Parent'[n] = stableState[n][2]
           /\ (stableState[n][1] = 0 \/ stableState[n][1] = omega)
           /\ (stableState[n][1] = 0 => stableState[n][2] = n)
           /\ (stableState[n][1] = omega => \A m \in Neighbors(n): stableState[m][1] = omega)

Spec == Spec /\ Safety /\ Convergence

WF_next(vars) ==
    \A state \in [<<Parent, Distance>> -> BOOLEAN]:
        \/ ~state[vars]
        \/ \E n \in Nodes, m \in Nodes:
               (m \in Neighbors(n)
                /\ Distance[n] > Distance[m]
                => state[<<[Parent EXCEPT ![n] = m], [Distance EXCEPT ![n] = Distance[m] + 1]>>])

=============================================================================