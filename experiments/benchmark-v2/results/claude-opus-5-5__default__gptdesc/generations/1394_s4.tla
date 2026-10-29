------------------------------ MODULE Github702 ------------------------------
(***************************************************************************)
(* Models a TLC issue in which an identifier becomes undefined inside an   *)
(* UNCHANGED expression during the computation of the next state.          *)
(*                                                                         *)
(* The module x_unchanged is instantiated with its variable x replaced by  *)
(* the constant-valued operator fizzbuzz. As a result, the conjunct        *)
(* UNCHANGED <<x, z>> in Next becomes UNCHANGED <<fizzbuzz, z>>. The       *)
(* subscript <<x, y, z>> in Spec becomes <<fizzbuzz, y, z>> in the same    *)
(* way. The variables y and z are substituted implicitly by the variables  *)
(* of the same name that this module declares.                             *)
(***************************************************************************)

VARIABLES y, z

fizzbuzz == 2

INSTANCE x_unchanged WITH x <- fizzbuzz

=============================================================================