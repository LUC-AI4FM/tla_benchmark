--------------------------- MODULE test56 ---------------------------
(***************************************************************************)
(* Test of subtle semantics of INSTANCE with substitution, comparing an   *)
(* instantiated action-related expression against a hand-written          *)
(* counterpart.                                                           *)
(***************************************************************************)
EXTENDS Naturals

  --------------------------- MODULE test56a ---------------------------
  VARIABLE u

  G(a) == a'

  H == ENABLED (G(u) = 9 - u)
  ======================================================================