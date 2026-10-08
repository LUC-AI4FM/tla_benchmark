------------------------------- MODULE DijkstraScholtenStub ------------------------------

CONSTANTS Nodes

VARIABLES nodeActivity, nodeColors, tokenPosition, tokenColor

(* --algorithm DijkstraScholtenStub
variables 
    nodeActivity = [n \in Nodes |-> FALSE],
    nodeColors   = [n \in Nodes |-> "white"],
    tokenPosition = CHOOSE n \in Nodes : TRUE,
    tokenColor  = "black";

begin
next == /\ nodeActivity' \in [Nodes -> BOOLEAN]
        /\ nodeColors' \in [Nodes -> {"white", "black"}]
        /\ tokenPosition' \in Nodes
        /\ tokenColor' = "black"
end algorithm *)

TypeInvariant ==
    /\ nodeActivity \in [Nodes -> BOOLEAN]
    /\ nodeColors \in [Nodes -> {"white", "black"}]
    /\ tokenPosition \in Nodes
    /\ tokenColor \in {"white", "black"}

Spec == TypeInvariant /\ WF_next(<<nodeActivity, nodeColors, tokenPosition, tokenColor>>)

=============================================================================