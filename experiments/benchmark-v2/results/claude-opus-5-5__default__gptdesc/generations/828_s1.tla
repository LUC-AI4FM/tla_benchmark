---------------------------- MODULE ApaCat ----------------------------
(***************************************************************************)
(* Thin wrapper around the Cat specification that supplies Apalache type   *)
(* annotations, so the original Cat module stays free of tool-specific     *)
(* annotations. All definitions (Init, Next, Spec, invariants and          *)
(* temporal properties) come from the instantiated Cat module.             *)
(***************************************************************************)
EXTENDS Naturals

CONSTANTS
    \* @type: Int;
    Number_Of_Boxes

VARIABLES
    \* @type: Int;
    cat_box,
    \* @type: Int;
    observed_box,
    \* @type: Str;
    direction

INSTANCE Cat
=============================================================================