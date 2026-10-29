------------------------------ MODULE APAclean ------------------------------
(***************************************************************************)
(* Apalache annotation wrapper for the specification "clean".             *)
(* Type annotations live here so that the original specification stays    *)
(* free of tool-specific annotations. No behavior, actions, temporal       *)
(* formulas or proofs are defined locally. Init, Next, Spec and all        *)
(* properties come from the instantiated module clean.                     *)
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