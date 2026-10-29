---------------------------- MODULE ApaCat ----------------------------
(***************************************************************************)
(* A thin wrapper around the Cat specification. It adds Apalache type     *)
(* annotations so that Cat itself does not need tool-specific             *)
(* annotations. Init, Next, Spec, the invariants and the liveness         *)
(* properties all come from Cat through the INSTANCE below.               *)
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