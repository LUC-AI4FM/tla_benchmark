--------------------------- MODULE test56 ---------------------------
(***************************************************************************)
(* Test of subtle semantics of INSTANCE with substitution.                 *)
(*                                                                         *)
(* Module test56a declares a variable u and defines H in terms of u.       *)
(* We instantiate it with u <- x.  We then compare the instantiated        *)
(* expression I!H with NotIBangH, a manually written counterpart obtained  *)
(* by substituting x for u in the definition of H.                         *)
(***************************************************************************)
EXTENDS Naturals, TLC

VARIABLE x

I == INSTANCE test56a WITH u <- x

(***************************************************************************)
(* Manually written counterpart of I!H.  This is the result of             *)
(* substituting x for u in the definition of H in module test56a.          *)
(***************************************************************************)
NotIBangH == x' = 9 - x

Init == x \in 1..3

Next == x' = 9 - x

Spec == Init /\ [][Next]_x

TypeOK == x \in 1..8

(***************************************************************************)
(* The instantiated expression I!H must equal NotIBangH on every step of   *)
(* every behavior, under stuttering semantics over x.                      *)
(***************************************************************************)
Property == [][I!H = NotIBangH]_x

THEOREM Spec => []TypeOK
THEOREM Spec => Property
=============================================================================