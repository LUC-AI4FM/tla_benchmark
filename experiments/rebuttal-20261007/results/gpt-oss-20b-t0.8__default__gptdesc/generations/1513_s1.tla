----------------------------- MODULE SimpleStateMachine -----------------------------
EXTENDS Naturals, TLC

CONSTANTS Nodes, Colors

VARIABLES active, color, tokenPos, tokenColor

(* --------------------------------------------------------------------------- *)
(* Type invariant: all variables have the correct domains                    *)
(* --------------------------------------------------------------------------- *)

TypeInvariant ==
    /\ active \in [Nodes -> BOOLEAN]
    /\ color  \in [Nodes -> Colors]
    /\ tokenPos \in Nodes
    /\ tokenColor \in Colors

(* --------------------------------------------------------------------------- *)
(* Initial state: any state satisfying the type invariant                     *)
(* --------------------------------------------------------------------------- *)

Init == TypeInvariant

(* --------------------------------------------------------------------------- *)
(* Next-state relation: any transition that preserves variable domains        *)
(* --------------------------------------------------------------------------- *)

Next ==
    /\ active'  \in [Nodes -> BOOLEAN]
    /\ color'   \in [Nodes -> Colors]
    /\ tokenPos' \in Nodes
    /\ tokenColor' \in Colors

vars == <<active, color, tokenPos, tokenColor>>

(* --------------------------------------------------------------------------- *)
(* Temporal specification: start in Init and forever satisfy stuttering-closed Next *)
(* --------------------------------------------------------------------------- *)

Spec == Init /\ [] [Next]_vars

=============================================================================