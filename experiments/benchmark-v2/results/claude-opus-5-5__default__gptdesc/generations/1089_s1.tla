---------------------------- MODULE APAstages ----------------------------
(***************************************************************************)
(* Apalache type annotations for the specification `stages`.               *)
(*                                                                         *)
(* This module is a thin wrapper. It declares typed constants and          *)
(* variables, then instantiates `stages`. The original specification       *)
(* therefore stays free of tool-specific annotations.                      *)
(*                                                                         *)
(* This module defines no behavior of its own. Init, Next, Spec and all    *)
(* invariants and properties come from the unnamed INSTANCE of `stages`    *)
(* below. They are visible here under their original names.                *)
(***************************************************************************)

EXTENDS Integers

CONSTANTS
    \* @type: Int;
    N,
    \* @type: Set(Str);
    Procs

VARIABLES
    \* @type: Str -> Int;
    stage,
    \* @type: Str -> Str;
    status

INSTANCE stages

=============================================================================