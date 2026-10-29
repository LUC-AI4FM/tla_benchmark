------------------------------- MODULE ApaCat -------------------------------
(***************************************************************************)
(* Thin wrapper around the Cat specification that supplies Apalache type   *)
(* annotations, so the original Cat module needs no tool-specific          *)
(* annotations.  Init, Next, Spec and all properties are imported from Cat *)
(* through the INSTANCE statement below.                                   *)
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