---------------------------- MODULE test216 ----------------------------
(***************************************************************************)
(* A test of module instantiation syntax and of the relationship between  *)
(* assumptions, theorems and definitions.                                   *)
(*                                                                          *)
(* The constant D is constrained by the assumption D + 0 = 42, which forces *)
(* D = 42.  The same fact is also stated as a theorem and as a definition.  *)
(*                                                                          *)
(* Module test216b is instantiated twice, once directly and once as the     *)
(* named instance I.  Both times E is replaced by D and y is replaced by 0. *)
(*                                                                          *)
(* History: updated for the change in how module names are handled in      *)
(* INSTANCE statements.                                                     *)
(***************************************************************************)
EXTENDS Naturals

  -------------------------- MODULE test216b --------------------------
  (*************************************************************************)
  (* The module that is instantiated.  It is nested here so that the       *)
  (* specification parses on its own.                                      *)
  (*************************************************************************)
  CONSTANT E
  VARIABLE y

  BProp == E + y = 42
  =====================================================================