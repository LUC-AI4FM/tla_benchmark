------------------------------- MODULE DijkstraScholtenStub -------------------------------
EXTENDS Integers, FiniteSets

CONSTANTS Nodes
ASSUME Nodes \in 1..n /\ n \in Nat /\ n > 0

VARIABLES nodeActivity, nodeColors, tokenPosition, tokenColor

Init == 
    /\ nodeActivity \in [Nodes -> BOOLEAN]
    /\ nodeColors \in [Nodes -> {"white", "black"}]
    /\ tokenPosition \in Nodes
    /\ tokenColor = "black"

Next ==
    \/ \E n \in Nodes : nodeActivity' = [nodeActivity EXCEPT ![n] = ~nodeActivity[n]]
    \/ \E n \in Nodes : nodeColors' = [nodeColors EXCEPT ![n] = IF nodeColors[n] = "white" THEN "black" ELSE "white"]
    \/ tokenPosition' \in Nodes
    \/ UNCHANGED <<nodeActivity, nodeColors, tokenColor>>

Spec == 
    /\ Init
    /\ [][Next]_<<nodeActivity, nodeColors, tokenPosition, tokenColor>>
    /\ WF_next(<<nodeActivity, nodeColors, tokenPosition, tokenColor>>)

TypeInvariant ==
    /\ nodeActivity \in [Nodes -> BOOLEAN]
    /\ nodeColors \in [Nodes -> {"white", "black"}]
    /\ tokenPosition \in Nodes
    /\ tokenColor = "black"

=============================================================================