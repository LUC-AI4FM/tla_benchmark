------------------------------ MODULE ParamInstanceTest ------------------------------
(***************************************************************************)
(* A small test specification for parametrized INSTANCE usage.  It is     *)
(* meant to test the handling of JSpec (a parametrized instance) versus   *)
(* ISpec (an instance with an explicit substitution).  It does not model  *)
(* a full algorithm.                                                       *)
(***************************************************************************)
EXTENDS Naturals

VARIABLE y

------------------------------- MODULE Inner -------------------------------
EXTENDS Naturals

VARIABLE x

InnerInit == x = 0

InnerNext == x' = (x + 1) % 5

Spec == InnerInit /\ [][InnerNext]_x
=============================================================================