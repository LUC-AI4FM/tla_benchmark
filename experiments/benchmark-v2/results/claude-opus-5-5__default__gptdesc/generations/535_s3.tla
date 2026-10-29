---------------------------- MODULE MC_Session5 ----------------------------
(***************************************************************************)
(* Minimal helper module layered over Session5.  It introduces no state   *)
(* variables, actions or temporal formulas of its own.  The behavior       *)
(* (variables, Init, Next, Spec, invariants and properties) is inherited   *)
(* unchanged from Session5.  This module only supplies concrete constant   *)
(* values for model checking.                                              *)
(***************************************************************************)
EXTENDS Session5, Integers

\* Numeric constant used as a minimal value in the model.
ConstMinValue == -99999

\* Set constant containing a single 3-tuple.
ConstTuples == { <<1, 2, 3>> }

=============================================================================