---------------------------- MODULE SimpleStateMachine ----------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS Nodes, Colors

VARIABLES active, color, tokenPos, tokenColor

vars == <<active, color, tokenPos, tokenColor>>

-----------------------------------------------------------------------------
(* Type Invariant *)

TypeOK ==
    /\ active \in [Nodes -> BOOLEAN]
    /\ color \in [Nodes -> Colors]
    /\ tokenPos \in Nodes
    /\ tokenColor \in Colors

-----------------------------------------------------------------------------
(* Initial State *)

Init ==
    /\ active \in [Nodes -> BOOLEAN]
    /\ color \in [Nodes -> Colors]
    /\ tokenPos \in Nodes
    /\ tokenColor \in Colors

-----------------------------------------------------------------------------
(* Next State Relation *)

Next ==
    /\ active' \in [Nodes -> BOOLEAN]
    /\ color' \in [Nodes -> Colors]
    /\ tokenPos' \in Nodes
    /\ tokenColor' \in Colors

-----------------------------------------------------------------------------
(* Specification *)

Spec == Init /\ [][Next]_vars

=============================================================================