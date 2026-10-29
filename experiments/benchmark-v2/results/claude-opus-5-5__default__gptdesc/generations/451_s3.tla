---- MODULE ParamInstanceTest ----
(***************************************************************************)
(* A small test specification for parametrized INSTANCE usage.            *)
(* It is meant to test how JSpec (from a parametrized instance with no    *)
(* explicit substitutions) is handled compared with ISpec (from an        *)
(* instance with the explicit substitution x <- y). It does not model a   *)
(* full algorithm.                                                         *)
(***************************************************************************)
EXTENDS Naturals

VARIABLE y

---------------------------- MODULE Inner ----------------------------------
VARIABLE x

IInit == x = 0

INext == x' = (x + 1) % 5

ISpec == IInit /\ [][INext]_x
=============================================================================