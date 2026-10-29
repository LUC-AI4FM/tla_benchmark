---------------------------- MODULE test64 ----------------------------
(***************************************************************************)
(* Wrapper module: declares a single variable y and instantiates module    *)
(* test64a, substituting its variable x with y.  The only top-level        *)
(* definition is Spec, which aliases the instantiated module's Spec.       *)
(*                                                                         *)
(* Note: the case of the instantiated module's name was changed because    *)
(* the previous form had become illegal.                                   *)
(***************************************************************************)

VARIABLE y

I == INSTANCE test64a WITH x <- y

Spec == I!Spec

=============================================================================