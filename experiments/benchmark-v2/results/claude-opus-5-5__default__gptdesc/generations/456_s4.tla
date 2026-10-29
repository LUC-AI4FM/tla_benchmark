---------------------------- MODULE test64 ----------------------------
(* Module name casing changed from the prior form, which had become illegal. *)

VARIABLE y

I == INSTANCE test64a WITH x <- y

Spec == I!Spec
=============================================================================