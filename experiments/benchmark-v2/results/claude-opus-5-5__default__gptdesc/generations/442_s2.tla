--------------------------- MODULE test56 ---------------------------
(***************************************************************************)
(* A small test of subtle INSTANCE semantics with substitution.            *)
(*                                                                         *)
(* Module test56a is instantiated as I, with u <- x.  The expression I!H   *)
(* is compared against NotIBangH, which writes out the expected result of  *)
(* the substitution by hand.                                               *)
(***************************************************************************)
EXTENDS Naturals

  ------------------------- MODULE test56a -------------------------
  VARIABLE u

  G(v) == v' = 9 - v

  H == /\ ENABLED (u' = 9 - u)
       /\ G(u)
  ==================================================================