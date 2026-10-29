--------------------------- MODULE test61 ---------------------------
(***************************************************************************)
(* Test of parametrized INSTANCE and of INSTANCE ... WITH substitution.   *)
(* Two instances of module test61a are defined:                            *)
(*   - J, in which the parameter x of test61a is set to the variable y     *)
(*     by an explicit WITH substitution.                                   *)
(*   - I(x), a parametrized instance with no WITH clause, in which x is    *)
(*     implicitly substituted by the operator argument x.                  *)
(* Operators of both instances are referenced, and an invariant restricts  *)
(* y to the range 0..4.                                                    *)
(***************************************************************************)
EXTENDS Naturals

VARIABLE y

  ---------------------------- MODULE test61a ----------------------------
  EXTENDS Naturals

  VARIABLE x

  AInit == x = 0

  ANext == x' = (x + 1) % 5

  AInRange == x \in 0..4

  AVal == x
  =========================================================================