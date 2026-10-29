---------------------------- MODULE APAclean ----------------------------
(***************************************************************************)
(* Apalache type annotations for the specification clean.tla.             *)
(*                                                                         *)
(* This wrapper module declares the constants and variables of clean with  *)
(* Apalache type annotations in comments, so that clean.tla itself stays   *)
(* free of tool-specific annotations. It then instantiates clean. Every    *)
(* behavior-related definition (Init, Next, Spec, invariants, liveness and *)
(* fairness conditions) comes from clean through the INSTANCE statement.   *)
(* No behavior, actions, temporal specification or proofs are defined in   *)
(* this module.                                                            *)
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