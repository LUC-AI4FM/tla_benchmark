------------------------------ MODULE APTokenRing ------------------------------
(***************************************************************************)
(* Thin wrapper around the TokenRing specification that supplies the      *)
(* Apalache type annotations for its constants and variables, so that     *)
(* the original TokenRing module can remain free of tool-specific         *)
(* annotations.                                                           *)
(*                                                                         *)
(* This module defines no algorithm, transition relation, or temporal     *)
(* properties of its own. Init, Next, Spec, all invariants, and all       *)
(* liveness properties come from TokenRing through the INSTANCE below.     *)
(*                                                                         *)
(* The INSTANCE has no explicit substitutions, so TokenRing's constants   *)
(* N and M and its variable c are implicitly bound to the identically    *)
(* named and typed declarations in this module.                           *)
(***************************************************************************)
EXTENDS Integers

CONSTANTS
    \* @type: Int;
    N,
    \* @type: Int;
    M

VARIABLES
    \* @type: Int -> Int;
    c

vars == << c >>

INSTANCE TokenRing

================================================================================