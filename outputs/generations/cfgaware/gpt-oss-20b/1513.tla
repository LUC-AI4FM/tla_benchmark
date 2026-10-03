------------------------------ MODULE SimpleStateMachine ------------------------------
EXTENDS Naturals, Sequences, TLC

CONSTANTS NodeSet, ColorSet

VARIABLES active, nodeColor, tokenPos, tokenColor

(* --------------------------------------------------------------------------- *)
(* Type constraints over the state variables                                   *)
(* --------------------------------------------------------------------------- *)

TypeOK ==
  /\ active ⊆ NodeSet
  /\ nodeColor ∈ [NodeSet -> ColorSet]
  /\ tokenPos ∈ NodeSet
  /\ tokenColor ∈ ColorSet

(* --------------------------------------------------------------------------- *)
(* Initial state: any assignment that satisfies the type constraints           *)
(* --------------------------------------------------------------------------- *)

Init == TypeOK

(* --------------------------------------------------------------------------- *)
(* Next-state relation: nondeterministically choose a successor state          *)
(* subject to the same type constraints.                                      *)
(* --------------------------------------------------------------------------- *)

Next ==
  \E a', c', p', t' :
    /\ a' ⊆ NodeSet
    /\ c' ∈ [NodeSet -> ColorSet]
    /\ p' ∈ NodeSet
    /\ t' ∈ ColorSet
    /\ active'   = a'
    /\ nodeColor'= c'
    /\ tokenPos'  = p'
    /\ tokenColor'= t'

(* --------------------------------------------------------------------------- *)
(* Set of variables used in the temporal specification                        *)
(* --------------------------------------------------------------------------- *)

vars == {active, nodeColor, tokenPos, tokenColor}

(* --------------------------------------------------------------------------- *)
(* Temporal specification: start in Init and thereafter satisfy stuttering-closed Next *)
(* --------------------------------------------------------------------------- *)

Spec == Init /\ [][Next]_vars

=============================================================================