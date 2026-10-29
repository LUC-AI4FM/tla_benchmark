---------------------------- MODULE APAclean ----------------------------
(***************************************************************************)
(* Apalache annotation wrapper for the specification "clean".             *)
(* Type annotations are given in comments here so that the module          *)
(* "clean" itself stays free of tool-specific annotations.                 *)
(*                                                                         *)
(* No behavior is defined locally. Init, Next, Spec and all invariants and *)
(* properties come from module "clean" through the INSTANCE below.         *)
(***************************************************************************)
EXTENDS Naturals

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
    hybrid

INSTANCE clean
=============================================================================