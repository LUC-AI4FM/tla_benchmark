---------------------------- MODULE APTokenRing ----------------------------
(***************************************************************************)
(* Wrapper around the TokenRing specification that supplies Apalache type *)
(* annotations, keeping the original TokenRing module free of             *)
(* tool-specific annotations.                                              *)
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

=============================================================================