--------------------------- MODULE test64 ---------------------------
(***************************************************************************)
(* Wrapper module that instantiates test64a, substituting the parameter    *)
(* x of test64a with the local state variable y. All behavioral            *)
(* definitions (initial condition, next-state relation, fairness, and the  *)
(* temporal specification) are inherited from test64a via instance I.      *)
(***************************************************************************)

VARIABLE y

I == INSTANCE test64a WITH x <- y

Spec == I!Spec

=============================================================================