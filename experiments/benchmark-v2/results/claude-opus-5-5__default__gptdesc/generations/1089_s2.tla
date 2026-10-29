------------------------------- MODULE APAstages -------------------------------
(***************************************************************************)
(* Apalache type annotations for the specification `stages`.               *)
(*                                                                         *)
(* This module is a thin wrapper: it declares the constants and variables  *)
(* of `stages` together with their Apalache type annotations, and then     *)
(* instantiates `stages`. This keeps the original specification free of    *)
(* tool-specific annotations.                                              *)
(*                                                                         *)
(* It defines no behavior, transition relation, temporal specification or  *)
(* correctness properties of its own. Init, Next, Spec and any invariants  *)
(* or liveness properties come from `stages` through the INSTANCE below.   *)
(*                                                                         *)
(* The constant and variable names here must match those declared in       *)
(* `stages`, so that the parameterless INSTANCE substitutes them by name.  *)
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
    \* @type: Int -> Int;
    count,
    \* @type: Str;
    status

(***************************************************************************)
(* Instantiate the original specification. Each constant and variable of   *)
(* `stages` is implicitly replaced by the typed declaration of the same    *)
(* name above. This brings all definitions of `stages` (Init, Next, Spec,  *)
(* and its invariants and properties) into scope unchanged.                *)
(***************************************************************************)
INSTANCE stages

================================================================================