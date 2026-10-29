------------------------------ MODULE ParamInstanceTest ------------------------------
(***************************************************************************)
(* A small test specification for parametrized INSTANCE usage.            *)
(*                                                                         *)
(* It declares a single variable y. It instantiates the inner module Inner *)
(* twice:                                                                  *)
(*   - J(x) == INSTANCE Inner  is parametrized, with no explicit           *)
(*     substitution (x is the parameter);                                  *)
(*   - I == INSTANCE Inner WITH x <- y  uses an explicit substitution.     *)
(* Both instantiations refer to the instantiated module's Spec operator.   *)
(* The point of the file is to test handling of JSpec versus ISpec, not to *)
(* model a full algorithm.                                                 *)
(***************************************************************************)
EXTENDS Naturals

  ---------------------------- MODULE Inner ----------------------------
  VARIABLE x

  InnerInit == x = 0

  InnerNext == x' = (x + 1) % 5

  Spec == InnerInit /\ [][InnerNext]_x
  ======================================================================