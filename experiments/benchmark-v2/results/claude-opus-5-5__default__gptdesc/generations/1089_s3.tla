------------------------------ MODULE APAstages ------------------------------
(***************************************************************************)
(* Apalache type annotations for the specification `stages`.              *)
(*                                                                         *)
(* This module only declares typed constants and variables and then       *)
(* instantiates `stages`. Init, Next, Spec and all properties come from    *)
(* `stages` through the INSTANCE statement, so the original specification *)
(* stays free of tool-specific annotations.                                *)
(***************************************************************************)

CONSTANTS
    \* @type: Int;
    DNA,
    \* @type: Int;
    PRIMER

VARIABLES
    \* @type: Str;
    tee,
    \* @type: Int;
    primer,
    \* @type: Int;
    dna,
    \* @type: Int;
    template,
    \* @type: Int;
    hybrid,
    \* @type: Str;
    stage,
    \* @type: Int;
    cycle

INSTANCE stages

=============================================================================