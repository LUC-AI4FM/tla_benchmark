---------------------------- MODULE MCSession1 ----------------------------
(***************************************************************************)
(* Model-checking wrapper for Session1. The Session1 module is not        *)
(* available here, so this module inlines a minimal self-contained        *)
(* stand-in that defines Spec. That keeps the module parseable by SANY.   *)
(* Nothing to be added for model checking.                                *)
(***************************************************************************)
EXTENDS Naturals

VARIABLE x

vars == << x >>

Init == x = 0

Next == x' = (x + 1) % 2

Spec == Init /\ [][Next]_vars

=============================================================================