---------------------------- MODULE APAstages ----------------------------
(***************************************************************************)
(* Apalache type annotations for the specification `stages`.               *)
(*                                                                         *)
(* This module only declares typed constants and variables and then        *)
(* instantiates `stages`. This keeps the original specification free of    *)
(* tool-specific annotations. The module adds no behavior, transition      *)
(* relation, temporal specification or correctness properties. Init, Next, *)
(* Spec and any invariants or properties come from `stages` through the    *)
(* INSTANCE below.                                                         *)
(***************************************************************************)

EXTENDS Integers

CONSTANTS
    \* @type: Int;
    N,
    \* @type: Set(Str);
    Stages

VARIABLES
    \* @type: Int -> Str;
    stage,
    \* @type: Int;
    count

INSTANCE stages

=============================================================================