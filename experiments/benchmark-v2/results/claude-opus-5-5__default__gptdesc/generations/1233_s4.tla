------------------------------- MODULE test61 -------------------------------
(***************************************************************************)
(* Test of parametrized INSTANCE and WITH substitution.                     *)
(*                                                                         *)
(* The module test61a is defined as an inner module so that this file is   *)
(* self-contained. It is instantiated twice:                               *)
(*   - I : with its parameter x substituted by the variable y;             *)
(*   - J : with no substitution, so its parameter x is implicitly          *)
(*         instantiated by the identically named variable x of this        *)
(*         module.                                                         *)
(***************************************************************************)
EXTENDS Naturals

  ------------------------------ MODULE test61a ------------------------------
  EXTENDS Naturals

  VARIABLE x

  Val     == x
  InitA   == x = 0
  Inc     == x' = (x + 1) % 5
  IsSmall == x \in 0..4
  ===========================================================================