---------------------------- MODULE test216 ----------------------------
(***************************************************************************)
(* Test of module instantiation syntax, and of the relationship between    *)
(* assumptions, theorems, and definitions.                                 *)
(*                                                                         *)
(* Updated to handle changes in how module names are written in INSTANCE   *)
(* statements.                                                             *)
(***************************************************************************)
EXTENDS Naturals

CONSTANT D

ASSUME D + 0 = 42

THEOREM D + 0 = 42

DIs42 == D + 0 = 42

INSTANCE test216b WITH E <- D, y <- 0

I == INSTANCE test216b WITH E <- D, y <- 0

=============================================================================