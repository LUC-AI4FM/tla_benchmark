---------------------------- MODULE APTokenRing ----------------------------
(***************************************************************************)
(* Thin wrapper that adds Apalache type annotations to TokenRing, so the   *)
(* original module stays free of tool-specific annotations.                *)
(*                                                                         *)
(* This module defines no algorithm of its own. Init, Next, Spec and all   *)
(* invariants and temporal properties come from TokenRing through the      *)
(* unnamed INSTANCE below.                                                 *)
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

\* Constants N, M and variable c are substituted implicitly by name.
INSTANCE TokenRing

=============================================================================