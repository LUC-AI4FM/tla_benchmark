---------------------------- MODULE MC_stages ----------------------------
(***************************************************************************)
(* Apalache type annotations for the specification `stages`.               *)
(*                                                                         *)
(* This module only declares typed constants and variables and then        *)
(* instantiates `stages`, so the original specification stays free of      *)
(* tool-specific annotations. It defines no behavior, transition relation, *)
(* temporal specification or correctness properties of its own. The        *)
(* Init, Next and Spec operators below delegate to the instantiated module.*)
(***************************************************************************)
EXTENDS Integers

CONSTANTS
    \* @type: Int;
    N,
    \* @type: Set(Str);
    Names

VARIABLES
    \* @type: Int;
    stage,
    \* @type: Str;
    label

vars == <<stage, label>>

\* Instantiate the original, annotation-free specification.
S == INSTANCE stages

\* Delegation only: all behavior is defined in `stages`.
Init == S!Init

Next == S!Next

Spec == S!Spec

=============================================================================