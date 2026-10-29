------------------------------ MODULE test61 ------------------------------
(***************************************************************************)
(* A test of parametrized INSTANCE and of INSTANCE ... WITH substitution.  *)
(* The instantiated module test61a is a nested submodule, so this file     *)
(* parses on its own.                                                      *)
(***************************************************************************)
EXTENDS Naturals

VARIABLE y

  ---------------------------- MODULE test61a ----------------------------
  EXTENDS Naturals

  VARIABLE x

  AInit == x = 0

  ANext == x' = (x + 1) % 5

  AInv == x \in 0..4

  Val == x
  ========================================================================