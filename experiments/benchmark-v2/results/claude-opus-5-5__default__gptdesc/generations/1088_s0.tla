---------------------------- MODULE APAclean ----------------------------
(***************************************************************************)
(* Apalache annotation wrapper for the specification `clean`.              *)
(*                                                                         *)
(* This module only adds Apalache type annotations (in comments) to the    *)
(* constants and variables. The original specification `clean` can then   *)
(* stay free of tool-specific annotations.                                 *)
(*                                                                         *)
(* This module defines no behavior, actions, temporal specification or     *)
(* proofs locally. The unnamed INSTANCE below imports all definitions from *)
(* `clean`, including Init, Next, Spec, its invariants and its properties. *)
(* Defining Init, Next or Spec here as well would clash with those         *)
(* imported names.                                                         *)
(***************************************************************************)
EXTENDS Naturals

CONSTANTS
    \* @type: Int;
    DNA,
    \* @type: Int;
    PRIMER

VARIABLES
    \* @type: Int;
    tee,
    \* @type: Int;
    primer,
    \* @type: Int;
    dna,
    \* @type: Int;
    template,
    \* @type: Int;
    hybrid

INSTANCE clean

=============================================================================