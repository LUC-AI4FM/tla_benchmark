------------------------------- MODULE ApaCat -------------------------------
(***************************************************************************)
(* Thin wrapper around the Cat specification that supplies Apalache type   *)
(* annotations, so that the original Cat module does not need any          *)
(* tool-specific annotations.                                              *)
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