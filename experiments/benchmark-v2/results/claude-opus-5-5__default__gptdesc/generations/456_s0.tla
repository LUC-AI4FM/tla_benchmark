---------------------------- MODULE test64 ----------------------------
(* Changed the name of this module from Test64 to test64 because the  *)
(* previous form of the module name had become illegal.               *)

VARIABLE y

I == INSTANCE test64a WITH x <- y

Spec == I!Spec
=========================================================================