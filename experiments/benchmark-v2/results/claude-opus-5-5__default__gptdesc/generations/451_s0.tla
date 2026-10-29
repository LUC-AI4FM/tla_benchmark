---------------------------- MODULE ParamInstanceTest ----------------------------
(***************************************************************************)
(* A small test specification for parametrized INSTANCE usage.             *)
(* It is meant to test the handling of JSpec (a parametrized instance with *)
(* no substitutions) versus ISpec (an instance with the explicit           *)
(* substitution x <- y). It does not model a full algorithm.               *)
(***************************************************************************)
EXTENDS Naturals

  ---------------------------- MODULE Inner ----------------------------
  (*************************************************************************)
  (* The module being instantiated. It has a single variable x that        *)
  (* counts from 0 to 4 and wraps around.                                  *)
  (*************************************************************************)
  VARIABLE x

  InnerInit == x = 0

  InnerNext == x' = (x + 1) % 5

  Spec == InnerInit /\ [][InnerNext]_x

  InnerTypeOK == x \in 0..4
  ======================================================================