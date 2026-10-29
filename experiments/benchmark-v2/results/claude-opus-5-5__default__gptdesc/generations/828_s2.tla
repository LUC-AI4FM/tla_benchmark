---------------------------- MODULE ApaCat ----------------------------
(***************************************************************************)
(* A thin wrapper around the specification Cat. It supplies Apalache type  *)
(* annotations for the constant and variables of Cat, so that the original *)
(* Cat module needs no tool-specific annotations.                          *)
(*                                                                         *)
(* This module defines no operators, actions, temporal properties or       *)
(* proofs of its own. Init, Next, Spec, the invariants, the liveness       *)
(* properties and the fairness conditions all come from Cat through the    *)
(* INSTANCE statement below.                                               *)
(***************************************************************************)
EXTENDS Naturals

CONSTANTS
    \* The number of boxes in which the cat may hide.
    \* @type: Int;
    Number_Of_Boxes

VARIABLES
    \* The box the cat is currently in.
    \* @type: Int;
    cat_box,
    \* The box that is currently being observed.
    \* @type: Int;
    observed_box,
    \* The direction in which the cat moves.
    \* @type: Str;
    direction

INSTANCE Cat

=============================================================================