---------------------------- MODULE test56 ----------------------------
(***************************************************************************)
(* Tests module instantiation semantics: how substituting x for the       *)
(* imported variable u interacts with parameterized operators whose       *)
(* bodies contain primed variables and ENABLED.                           *)
(***************************************************************************)
EXTENDS Naturals, TLC

VARIABLE x

(***************************************************************************)
(* Instantiate test56a, replacing its variable u with x.                  *)
(***************************************************************************)
I == INSTANCE test56a WITH u <- x

(***************************************************************************)
(* Initial state: x is nondeterministically 1, 2 or 3.                    *)
(***************************************************************************)
Init == x \in 1..3

(***************************************************************************)
(* Next-state relation: x oscillates between x and 9 - x.                 *)
(***************************************************************************)
Next == x' = 9 - x

(***************************************************************************)
(* A locally written formula that combines a stuttering condition with    *)
(* a call to the instantiated operator G. Its arguments are x and an      *)
(* expression involving x's successor value.                              *)
(***************************************************************************)
NotIBangH == (x' = x) /\ I!G(x, x' + 1)

(***************************************************************************)
(* Temporal specification.                                                 *)
(***************************************************************************)
Spec == Init /\ [][Next]_x

(***************************************************************************)
(* Property: in every step, the instantiated operator I!H equals the      *)
(* locally defined NotIBangH.                                              *)
(***************************************************************************)
Property == [][I!H = NotIBangH]_x

THEOREM Spec => Property
=============================================================================