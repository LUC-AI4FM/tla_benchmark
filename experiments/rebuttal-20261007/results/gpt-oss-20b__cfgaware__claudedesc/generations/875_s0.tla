------------------------------ MODULE RandomSpanningTree ------------------------------
EXTENDS Naturals

CONSTANTS Nodes, Root, MaxCardinality, Edges

ASSUME
    /\ Root \in Nodes
    /\ MaxCardinality \in Nat
    /\ MaxCardinality >= Cardinal