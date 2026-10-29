---------------------------- MODULE APATokenRing ----------------------------
(***************************************************************************)
(* Thin wrapper around the TokenRing specification that supplies Apalache *)
(* type annotations. The original TokenRing module stays free of          *)
(* tool-specific annotations.                                             *)
(*                                                                         *)
(* This module defines no algorithm, transition relation or temporal      *)
(* properties of its own. Init, Next, Spec, and all invariants and        *)
(* liveness properties come from TokenRing through the INSTANCE below.    *)
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

(***************************************************************************)
(* Instantiate TokenRing without explicit substitutions. The constants N  *)
(* and M and the variable c are matched to the identically named          *)
(* parameters of TokenRing.                                               *)
(***************************************************************************)
INSTANCE TokenRing

=============================================================================