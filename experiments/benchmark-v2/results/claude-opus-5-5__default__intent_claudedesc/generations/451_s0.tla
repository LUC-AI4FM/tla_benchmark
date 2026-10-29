------------------------------ MODULE InstanceTest ------------------------------
(***************************************************************************)
(* Tests module instantiation with parameter substitution. A base module   *)
(* (Counter) is instantiated in two ways:                                  *)
(*   1. Operator-based: I(p) == INSTANCE Counter WITH n <- p, invoked      *)
(*      with the local variable x, i.e. I(x).                              *)
(*   2. Direct substitution: J == INSTANCE Counter WITH n <- x.            *)
(* Both must yield the same set of behaviors.                              *)
(***************************************************************************)
EXTENDS Naturals

  ---------------------------- MODULE Counter ----------------------------
  (*************************************************************************)
  (* Base module: a bounded counter over the parameter variable n.         *)
  (*************************************************************************)
  EXTENDS Naturals

  VARIABLE n

  CInit == n = 0

  CNext == n' = (n + 1) % 5

  CSpec == CInit /\ [][CNext]_n

  CTypeOK == n \in 0..4
  ========================================================================